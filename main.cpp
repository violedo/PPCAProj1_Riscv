#include <iostream>
#include <cstdio>
#include <cstring>
#include <ctime>
using namespace std;

int signed_extend(int data,int bits)
{
    if (data&(1<<(bits-1)))
        data|=0xffffffff>>(bits-1)<<(bits-1);
    return data;
}

class Riscv{
private:


    class Memory{
    private:
        unsigned char context[0x400000];
    public:
        Memory()
        {
            memset(context,0,0x400000);
        }
        unsigned char operator[](int addr)
        {
            return context[addr];
        }
        void change(int x,int pos)
        {
            context[pos]=(unsigned char)x;
        }
    };

    class Reg{
    private:
        int context;
    public:
        Reg()
        {
            context=0;
        }
        int write()
        {
            return context;
        }
        void operator=(int ch)
        {
            context=ch;
        }
        void operator=(Reg p)
        {
            context=p.context;
        }
        void operator+=(int ch)
        {
            context+=ch;
        }

    };

    Reg reg[32];
    Reg pc;
    Memory memory;

    int count=0;
    //int before=0;

    class Order{
    protected:
        int rd,rs1,rs2;
        int ins,imm,func3,func7;
        Reg* reg,*pc;
        Memory* memory;
    public:
        Order(int x,Reg* r,Reg* p,Memory* m){
            ins=x;reg=r;pc=p;memory=m;
        }
        ~Order(){}
        virtual void ID()=0;
        virtual pair<bool,unsigned int> Ex()=0;
        virtual void MA()=0;
        virtual void WB()=0;
    };

    class U:public Order{
    private:
        int pc_context;
    public:
        U(int x,Reg* r,Reg* p,Memory* m):Order(x,r,p,m){}

        void ID(){
            rd=(ins>>7)&31;
            imm=(ins>>12)<<12;
        }

        pair<bool,unsigned int> Ex(){
            if ((ins&127)==0x37)
            {}
            else {
                pc_context=pc->write();
                pc_context+=imm;
            }
            pair<bool,unsigned int> res;
            res.first=0;
            res.second=0;
            return res;
        }

        void MA(){}

        void WB(){
            if ((ins&127)==0x37)
            {
                *pc+=4;
                if (rd==0)
                    return;
                reg[rd]=imm;
            }
            else {
                *pc=pc_context;
                if (rd==0)
                    return;
                reg[rd]=pc_context;
            }
        }
    };
    class J:public Order{
    private:
        int pc_context;
        int rd_context;
    public:
        J(int x,Reg* r,Reg* p,Memory* m):Order(x,r,p,m){}

        void ID(){
            rd=(ins>>7)&31;
            imm=(((ins>>12)&255)<<12)+(((ins>>20)&1)<<11)+(((ins>>21)&1023)<<1)+(((ins>>31)&1)<<20);
            imm=signed_extend(imm,21);
        }

        pair<bool,unsigned int> Ex(){
            pc_context=pc->write();
            rd_context=pc_context+4;
            pc_context+=imm;
            pair<bool,unsigned int> res;
            res.first=0;
            res.second=0;
            return res;
        }

        void MA(){}

        void WB(){
            *pc=pc_context;
            if (rd==0)
                return;
            reg[rd]=rd_context;
        }
    };
    class I:public Order{
    private:
        int pc_context;
        int rs1_context;
        int rd_context;
        int addr;
    public:
        I(int x,Reg* r,Reg* p,Memory* m):Order(x,r,p,m){}

        void ID(){
            rd=(ins>>7)&31;
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            imm=(ins>>20)&4095;
            imm=signed_extend(imm,12);
        }

        pair<bool,unsigned int> Ex(){
            switch (ins&127){
                case 0x67:{
                    pc_context=pc->write();
                    rd_context=pc_context+4;
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    pc_context=rs1_context+imm;
                    pc_context=(pc_context>>1)<<1;
                    break;
                }
                case 0x3:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    addr=rs1_context+imm;
                    break;
                }
                case 0x13:{
                    switch (func3){
                        case 0:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=imm+rs1_context;
                            break;
                        }
                        case 2:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=(rs1_context<imm)?1:0;
                            break;
                        }
                        case 3:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=((unsigned int)rs1_context<(unsigned int)imm)?1:0;
                            break;
                        }
                        case 4:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=rs1_context^imm;
                            break;
                        }
                        case 6:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=rs1_context|imm;
                            break;
                        }
                        case 7:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=rs1_context&imm;
                            break;
                        }
                        case 1:{
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            rd_context=rs1_context<<imm;
                            break;
                        }
                        case 5:
                            if (rs1==0)
                                rs1_context=0;
                            else rs1_context=reg[rs1].write();
                            if ((imm>>9)==0)
                            {
                                rd_context=(unsigned int)rs1_context>>imm;
                            }
                            else {
                                imm&=31;
                                rd_context=rs1_context>>imm;
                            }
                            break;
                    }
                    break;
                }
            }
            pair<bool,unsigned int> res;
            res.first=0;
            res.second=0;
            return res;
        }

        void MA(){
            switch (ins&127){
                case 0x67:break;
                case 0x3:{
                    switch (func3){
                        case 0:{
                            rd_context=(int)memory->operator[](addr);
                            rd_context=signed_extend(rd_context,8);
                            break;
                        }
                        case 1:{
                            rd_context=((int)memory->operator[](addr+1)<<8)+(int)memory->operator[](addr);
                            rd_context=signed_extend(rd_context,16);
                            break;
                        }
                        case 2:{
                            rd_context=((int)memory->operator[](addr+3)<<24)+((int)memory->operator[](addr+2)<<16)+((int)memory->operator[](addr+1)<<8)+(int)memory->operator[](addr);
                            break;
                        }
                        case 4:{
                            rd_context=(int)memory->operator[](addr);
                            break;
                        }
                        case 5:{
                            rd_context=((int)memory->operator[](addr+1)<<8)+(int)memory->operator[](addr);
                            break;
                        }
                    }
                    break;
                }
                case 0x13:break;
            }
        }

        void WB(){
            switch (ins&127){
                case 0x67:{
                    *pc=pc_context;
                    if (rd==0)
                        return;
                    reg[rd]=rd_context;
                    break;
                }
                case 0x3:{
                    *pc+=4;
                    if (rd==0)
                        return;
                    reg[rd]=rd_context;

                    break;
                }
                case 0x13:{
                    *pc+=4;
                    if (rd==0)
                        return;
                    reg[rd]=rd_context;
                    break;
                }
            }
        }
    };
    class B:public Order{
    private:
        int rs1_context,rs2_context,pc_context;
    public:
        B(int x,Reg* r,Reg* p,Memory* m):Order(x,r,p,m){}

        void ID(){
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            rs2=(ins>>20)&31;
            imm=(((ins>>7)&1)<<11)+(((ins>>8)&15)<<1)+(((ins>>25)&63)<<5)+(((ins>>31)&1)<<12);
            imm=signed_extend(imm,13);
        }

        pair<bool,unsigned int> Ex(){
            if (rs1==0)
                rs1_context=0;
            else rs1_context=reg[rs1].write();
            if (rs2==0)
                rs2_context=0;
            else rs2_context=reg[rs2].write();
            pc_context=pc->write();
            switch (func3){
                case 0:{

                    if (rs1_context==rs2_context)
                        pc_context+=imm;
                    else pc_context+=4;
                    break;
                }
                case 1:{
                    if (rs1_context!=rs2_context)
                        pc_context+=imm;
                    else pc_context+=4;
                    break;
                }
                case 4:{
                    if (rs1_context<rs2_context)
                        pc_context+=imm;
                    else pc_context+=4;
                    break;
                }
                case 5:{
                    if (rs1_context>=rs2_context)
                        pc_context+=imm;
                    else pc_context+=4;
                    break;
                }
                case 6:{
                    if ((unsigned int)rs1_context<(unsigned int)rs2_context)
                        pc_context+=imm;
                    else pc_context+=4;
                    break;
                }
                case 7:{
                    if ((unsigned int)rs1_context>=(unsigned int)rs2_context)
                        pc_context+=imm;
                    else pc_context+=4;
                    break;
                }
            }
            pair<bool,unsigned int> res;
            res.first=0;
            res.second=0;
            return res;
        }

        void MA(){}

        void WB(){
            *pc=pc_context;
        }
    };
    class S:public Order{
    private:
        int rs2_context;
        int rs1_context;
        int addr;
    public:
        S(int x,Reg* r,Reg* p,Memory* m):Order(x,r,p,m){}

        void ID(){
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            rs2=(ins>>20)&31;
            imm=((ins>>7)&31)+(((ins>>25)&127)<<5);
            imm=signed_extend(imm,12);
        }

        pair<bool,unsigned int> Ex(){
            if (rs1==0)
                rs1_context=0;
            else rs1_context=reg[rs1].write();
            if (rs2==0)
                rs2_context=0;
            else rs2_context=reg[rs2].write();
            addr=rs1_context+imm;
            pair<bool,unsigned int> res;
            res.first=0;
            res.second=0;
            if (addr==0x30004)
            {
                res.second=reg[10].write()&255;
                res.first=1;
            }
            return res;
        }

        void MA(){
            switch (func3) {
                case 0:{
                    memory->change((rs2_context&255),addr);
                    break;
                }
                case 1:{
                    memory->change((rs2_context>>8)&255,addr+1);
                    memory->change(rs2_context&255,addr);
                    break;
                }
                case 2:{
                    memory->change((rs2_context>>24)&255,addr+3);
                    memory->change((rs2_context>>16)&255,addr+2);
                    memory->change((rs2_context>>8)&255,addr+1);
                    memory->change(rs2_context&255,addr);
                    break;
                }
            }
        }

        void WB(){
            *pc+=4;
        }
    };
    class R:public Order{
    private:
        int rs1_context,rs2_context,rd_context;
    public:
        R(int x,Reg* r,Reg* p,Memory* m):Order(x,r,p,m){}

        void ID(){
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            rs2=(ins>>20)&31;
            rd=(ins>>7)&31;
            func7=(ins>>25)&127;
        }

        pair<bool,unsigned int> Ex(){
            switch (func3){
                case 0:{
                    if (func7)
                    {
                        if (rs1==0)
                            rs1_context=0;
                        else rs1_context=reg[rs1].write();
                        if (rs2==0)
                            rs2_context=0;
                        else rs2_context=reg[rs2].write();
                        rd_context=rs1_context-rs2_context;
                    }
                    else {
                        if (rs1==0)
                            rs1_context=0;
                        else rs1_context=reg[rs1].write();
                        if (rs2==0)
                            rs2_context=0;
                        else rs2_context=reg[rs2].write();
                        rd_context=rs1_context+rs2_context;
                    }
                    break;
                }
                case 1:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    rd_context=rs1_context<<(rs2_context&31);
                    break;
                }
                case 2:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    rd_context=(rs1_context<rs2_context)?1:0;
                    break;
                }
                case 3:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    rd_context=((unsigned int)rs1_context<(unsigned int)rs2_context)?1:0;
                    break;
                }

                case 4:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    rd_context=rs1_context^rs2_context;
                    break;
                }
                case 5: {
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    if (func7)
                        rd_context=rs1_context>>(rs2_context&31);
                    else rd_context=(unsigned int)rs1_context>>(rs2_context&31);
                    break;
                }
                case 6:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    rd_context=rs1_context|rs2_context;
                    break;
                }
                case 7:{
                    if (rs1==0)
                        rs1_context=0;
                    else rs1_context=reg[rs1].write();
                    if (rs2==0)
                        rs2_context=0;
                    else rs2_context=reg[rs2].write();
                    rd_context=rs1_context&rs2_context;
                    break;
                }

            }
            pair<bool,unsigned int> res;
            res.first=0;
            res.second=0;
            return res;
        }

        void MA(){}

        void WB(){
            *pc+=4;
            if (rd==0)
                return;
            reg[rd]=rd_context;

        }
    };

    struct Ex_buffer{
        bool ending;
        unsigned int res;
        Order* inst;
    };
    int IF()
    {
        int x=(memory[pc.write()+3]<<24)+(memory[pc.write()+2]<<16)+(memory[pc.write()+1]<<8)+memory[pc.write()];
        return x;
    }
    Order* ID(int order)
    {
        Order *p;
        int a=order&127;
        if (count==101)
            int r=0;
        switch (a){
            case 0x37:
            case 0x17:p = new U(order,reg,&pc,&memory);break;
            case 0x6f:p=new J(order,reg,&pc,&memory);break;
            case 0x67:p=new I(order,reg,&pc,&memory);break;
            case 0x63:p=new B(order,reg,&pc,&memory);break;
            case 0x3:p=new I(order,reg,&pc,&memory);break;
            case 0x23:p=new S(order,reg,&pc,&memory);break;
            case 0x13:p=new I(order,reg,&pc,&memory);break;
            case 0x33:p=new R(order,reg,&pc,&memory);break;
        }
        p->ID();
        return p;
    }
    Ex_buffer Ex(Order* p)
    {
        pair<bool,unsigned int> x=p->Ex();
        Ex_buffer m;
        m.inst=p;
        m.res=x.second;
        m.ending=x.first;
        return m;
    }
    Order* MA(Order* p)
    {
        p->MA();
        return p;
    }
    Order* WB(Order* p)
    {
        p->WB();
        return p;
    }
    void test()
    {
        /*if (reg[10].write()!=before)
        {
            cout<<reg[10].write()<<' '<<count<<' '<<pc.write()<<endl;
            before=reg[10].write();
        }*/
        cout<<count<<"   "<<pc.write()<<' '<<(int)memory[5860]<<' ';
        for (int i=0;i<32;++i)
            cout<<reg[i].write()<<' ';
        cout<<endl;
    }
public:

    void run()
    {
        Ex_buffer ex_buffer;
        ex_buffer.ending=0;
        while (!ex_buffer.ending)
        {

            int order=IF();
            Order* ID_buffer=ID(order);
            ex_buffer=Ex(ID_buffer);
            Order* MA_buffer=MA(ex_buffer.inst);
            Order* WB_buffer=WB(MA_buffer);
            //test();
            ++count;
            delete MA_buffer;
        }

        cout<<ex_buffer.res;
    }
    void get_memory()
    {
        char ch;
        int addr=0;
        int tmp;
        while (cin>>ch)
        {
            if ((ch>='0'&&ch<='9')||(ch>='A'&&ch<='F'))
            {
                cin>>hex>>tmp;
                if (ch>='A'&&ch<='F')
                    tmp+=(ch-'A'+10)*16;
                else tmp+=(ch-'0')*16;
                memory.change(tmp,addr++);
            }
            else if (ch=='@')
            {
                cin>>hex>>addr;
            }
        }
    }
};









Riscv riscv;


int main() {
    /*char n[20];
    strcpy(n,
    // "basicopt1.data"
    //"bulgarian.data"
    // "magic.data"
    "pi.data"
    // "queens.data"
    // "array_test1.data"
    //"array_test2.data"
    //"expr.data"
    //"gcd.data"
    //"hanoi.data"
    //"lvalue2.data"
    //"manyarguments.data"
    //"multiarray.data"
    //"naive.data"
    //"qsort.data"
    //"statement_test.data"
    //"superloop.data"
    //"tak.data"
    );
    freopen(n, "r", stdin);
    time_t start,ending;
    start=time(NULL);*/
    riscv.get_memory();
    riscv.run();
    /*ending=time(NULL);
    cout<<"time spent "<<ending-start<<endl;*/
    return 0;
}
