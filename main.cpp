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

unsigned int predict_succ=0,predict_fail=0;
class Riscv{
    friend class Order;
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
        uint8_t lock;
        uint8_t load_lock;
    public:
        Reg()
        {
            context=0;
            lock=0;
            load_lock=0;
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
        bool locked()
        {
            return (lock)? 1:0;
        }
        void do_lock()
        {
            ++lock;
        }
        void unlock()
        {
            if (lock)
                --lock;
        }bool load_locked()
        {
            return (load_lock)? 1:0;
        }
        void do_load_lock()
        {
            ++load_lock;
        }
        void un_load_lock()
        {
            if (load_lock)
                --load_lock;
        }
    };

    struct Hash{
        int pc=0;
        int predict=0;
        int jump=0;
    };

    Reg reg[32];
    Reg pc;
    Memory memory;
    Hash hash[12281];

    int count=0;

    class Order{
    protected:
        int rd,rs1,rs2,pc;
        int ins,imm,func3,func7;
        Reg* reg;
        Memory* memory;
        Riscv* riscv;
    public:
        Order(int x,Reg* r,int p,Memory* m,Riscv* ri){
            ins=x;reg=r;pc=p;memory=m;riscv=ri;
        }
        ~Order(){}
        virtual void ID()=0;
        virtual void Ex()=0;
        virtual void MA()=0;
        virtual void WB()=0;
    };

    class U:public Order{
    private:
        int pc_context;
    public:
        U(int x,Reg* r,int p,Memory* m,Riscv* ri):Order(x,r,p,m,ri){}

        void ID(){
            rd=(ins>>7)&31;
            imm=(ins>>12)<<12;
        }

       void Ex(){
            riscv->ex_out.success=1;
            if ((ins&127)==0x37&&rd!=0)
            {
                riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=imm;
            }
            else {
                pc_context=pc;
                pc_context+=imm;
                riscv->ex_out.change=1;
                riscv->ex_out.changeto=pc_context;
                if (rd!=0)
                {
                    riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                    riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=pc_context;
                }
            }
            riscv->ex_out.res=0;
            riscv->ex_out.ending=0;
        }

        void MA(){}

        void WB(){
            if ((ins&127)==0x37)
            {
                if (rd==0)
                    return;
                reg[rd]=imm;
            }
            else {
                if (rd==0)
                    return;
                reg[rd]=pc_context;
            }
            riscv->ex_buffer.reg_context[0]=riscv->ex_buffer.reg_context[1];
            riscv->ex_buffer.reg_context[1]=0;
            riscv->ex_buffer.reg[0]=riscv->ex_buffer.reg[1];
            riscv->ex_buffer.reg[1]=0;
            if (riscv->ex_buffer.count)
                --riscv->ex_buffer.count;
        }
    };
    class J:public Order{
    private:
        int pc_context;
        int rd_context;
    public:
        J(int x,Reg* r,int p,Memory* m,Riscv* ri):Order(x,r,p,m,ri){}

        void ID(){
            rd=(ins>>7)&31;
            imm=(((ins>>12)&255)<<12)+(((ins>>20)&1)<<11)+(((ins>>21)&1023)<<1)+(((ins>>31)&1)<<20);
            imm=signed_extend(imm,21);
        }

        void Ex(){
            riscv->ex_out.success=1;
            pc_context=pc;
            rd_context=pc_context+4;
            pc_context+=imm;
            riscv->ex_out.change=1;
            riscv->ex_out.changeto=pc_context;
            if (rd!=0)
            {
                riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=rd_context;
            }
            riscv->ex_out.res=0;
            riscv->ex_out.ending=0;
        }

        void MA(){}

        void WB(){
            if (rd==0)
                return;
            reg[rd]=rd_context;
            riscv->ex_buffer.reg_context[0]=riscv->ex_buffer.reg_context[1];
            riscv->ex_buffer.reg_context[1]=0;
            riscv->ex_buffer.reg[0]=riscv->ex_buffer.reg[1];
            riscv->ex_buffer.reg[1]=0;
            if (riscv->ex_buffer.count)
                --riscv->ex_buffer.count;
        }
    };
    class I:public Order{
    private:
        int pc_context;
        int rs1_context;
        int rd_context;
        int addr;
    public:
        I(int x,Reg* r,int p,Memory* m,Riscv* ri):Order(x,r,p,m,ri){}

        void ID(){
            rd=(ins>>7)&31;
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            imm=(ins>>20)&4095;
            imm=signed_extend(imm,12);
        }

        void Ex(){
            if (reg[rs1].load_locked())
            {
                riscv->ex_out.success=0;
                riscv->ex_out.res=0;
                riscv->ex_out.ending=0;
                return;
            }
            else riscv->ex_out.success=1;
            if (rs1==0)
                rs1_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs1_context=reg[rs1].write();
                        break;
                    }
                    case 1:{
                        if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                    case 2:{
                        if (rs1==riscv->ex_buffer.reg[1])
                            rs1_context=riscv->ex_buffer.reg_context[1];
                        else if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                }
            }
            switch (ins&127){
                case 0x67:{
                    pc_context=pc;
                    rd_context=pc_context+4;
                    if (rd!=0)
                    {
                        riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                        riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=rd_context;
                    }
                    pc_context=rs1_context+imm;
                    pc_context=(pc_context>>1)<<1;
                    riscv->ex_out.change=1;
                    riscv->ex_out.changeto=pc_context;
                    break;
                }
                case 0x3:{
                    addr=rs1_context+imm;
                    reg[rd].do_load_lock();
                    break;
                }
                case 0x13:{
                    switch (func3){
                        case 0:{
                            rd_context=imm+rs1_context;
                            break;
                        }
                        case 2:{
                            rd_context=(rs1_context<imm)?1:0;
                            break;
                        }
                        case 3:{
                            rd_context=((unsigned int)rs1_context<(unsigned int)imm)?1:0;
                            break;
                        }
                        case 4:{
                            rd_context=rs1_context^imm;
                            break;
                        }
                        case 6:{
                            rd_context=rs1_context|imm;
                            break;
                        }
                        case 7:{
                            rd_context=rs1_context&imm;
                            break;
                        }
                        case 1:{
                            rd_context=rs1_context<<imm;
                            break;
                        }
                        case 5: {
                            if ((imm >> 9) == 0) {
                                rd_context = (unsigned int) rs1_context >> imm;
                            } else {
                                imm &= 31;
                                rd_context = rs1_context >> imm;
                            }
                            break;
                        }
                    }
                    if (rd!=0)
                    {
                        riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                        riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=rd_context;
                    }
                    break;
                }
            }
            riscv->ex_out.res=0;
            riscv->ex_out.ending=0;
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
                    reg[rd].un_load_lock();
                    riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                    riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=rd_context;
                    break;
                }
                case 0x13:break;
            }
        }

        void WB(){
            if (rd==0)
                return;
            reg[rd]=rd_context;
            riscv->ex_buffer.reg_context[0]=riscv->ex_buffer.reg_context[1];
            riscv->ex_buffer.reg_context[1]=0;
            riscv->ex_buffer.reg[0]=riscv->ex_buffer.reg[1];
            riscv->ex_buffer.reg[1]=0;
            if (riscv->ex_buffer.count)
                --riscv->ex_buffer.count;
        }
    };
    class B:public Order{
    private:
        int rs1_context,rs2_context,pc_context;
        int jump_choice;
        int the_other;
    public:
        B(int x,Reg* r,int p,Memory* m,Riscv* ri,int j):Order(x,r,p,m,ri)
        {
            jump_choice=j;
        }

        void ID(){
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            rs2=(ins>>20)&31;
            imm=(((ins>>7)&1)<<11)+(((ins>>8)&15)<<1)+(((ins>>25)&63)<<5)+(((ins>>31)&1)<<12);
            imm=signed_extend(imm,13);
        }

        void Ex(){
            if (reg[rs1].load_locked()||reg[rs2].load_locked())
            {
                riscv->ex_out.success=0;
                riscv->ex_out.res=0;
                riscv->ex_out.ending=0;
                return;
            }
            else riscv->ex_out.success=1;
            if (rs1==0)
                rs1_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs1_context=reg[rs1].write();
                        break;
                    }
                    case 1:{
                        if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                    case 2:{
                        if (rs1==riscv->ex_buffer.reg[1])
                            rs1_context=riscv->ex_buffer.reg_context[1];
                        else if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                }
            }
            if (rs2==0)
                rs2_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs2_context=reg[rs2].write();
                        break;
                    }
                    case 1:{
                        if (rs2==riscv->ex_buffer.reg[0])
                            rs2_context=riscv->ex_buffer.reg_context[0];
                        else rs2_context=reg[rs2].write();
                        break;
                    }
                    case 2:{
                        if (rs2==riscv->ex_buffer.reg[1])
                            rs2_context=riscv->ex_buffer.reg_context[1];
                        else if (rs2==riscv->ex_buffer.reg[0])
                            rs2_context=riscv->ex_buffer.reg_context[0];
                        else rs2_context=reg[rs2].write();
                        break;
                    }
                }
            }
            pc_context=pc;
            int i;
            for (i=0;i<10000;i++)
             {
                if (!riscv->hash[(pc + i * i) % 12281].pc) {
                    riscv->hash[(pc + i * i) % 12281].pc = pc;
                    break;
                }
                if (riscv->hash[(pc + i * i) % 12281].pc == pc)
                    break;
            }
            if (!riscv->hash[(pc+i*i)%12281].jump)
                riscv->hash[(pc+i*i)%12281].jump=pc+imm;
            if (jump_choice==pc+4)
                the_other=pc+imm;
            if (jump_choice==pc+imm)
                the_other=pc+4;
            switch (func3){
                case 0:{
                    if (rs1_context==rs2_context)
                    {
                        pc_context+=imm;
                        if (riscv->hash[(pc+i*i)%12281].predict<2)
                            ++riscv->hash[(pc+i*i)%12281].predict;
                    }
                    else {
                        pc_context+=4;
                        if (riscv->hash[(pc+i*i)%12281].predict>-1)
                            --riscv->hash[(pc+i*i)%12281].predict;
                    }
                    break;
                }
                case 1:{
                    if (rs1_context!=rs2_context)
                    {
                        pc_context+=imm;
                        if (riscv->hash[(pc+i*i)%12281].predict<2)
                            ++riscv->hash[(pc+i*i)%12281].predict;
                    }
                    else {
                        pc_context+=4;
                        if (riscv->hash[(pc+i*i)%12281].predict>-1)
                            --riscv->hash[(pc+i*i)%12281].predict;
                    }
                    break;
                }
                case 4:{
                    if (rs1_context<rs2_context)
                    {
                        pc_context+=imm;
                        if (riscv->hash[(pc+i*i)%12281].predict<2)
                            ++riscv->hash[(pc+i*i)%12281].predict;
                    }
                    else {
                        pc_context+=4;
                        if (riscv->hash[(pc+i*i)%12281].predict>-1)
                            --riscv->hash[(pc+i*i)%12281].predict;
                    }
                    break;
                }
                case 5:{
                    if (rs1_context>=rs2_context)
                    {
                        pc_context+=imm;
                        if (riscv->hash[(pc+i*i)%12281].predict<2)
                            ++riscv->hash[(pc+i*i)%12281].predict;
                    }
                    else {
                        pc_context+=4;
                        if (riscv->hash[(pc+i*i)%12281].predict>-1)
                            --riscv->hash[(pc+i*i)%12281].predict;
                    }
                    break;
                }
                case 6:{
                    if ((unsigned int)rs1_context<(unsigned int)rs2_context)
                    {
                        pc_context+=imm;
                        if (riscv->hash[(pc+i*i)%12281].predict<2)
                            ++riscv->hash[(pc+i*i)%12281].predict;
                    }
                    else {
                        pc_context+=4;
                        if (riscv->hash[(pc+i*i)%12281].predict>-1)
                            --riscv->hash[(pc+i*i)%12281].predict;
                    }
                    break;
                }
                case 7:{
                    if ((unsigned int)rs1_context>=(unsigned int)rs2_context)
                    {
                        pc_context+=imm;
                        if (riscv->hash[(pc+i*i)%12281].predict<2)
                            ++riscv->hash[(pc+i*i)%12281].predict;
                    }
                    else {
                        pc_context+=4;
                        if (riscv->hash[(pc+i*i)%12281].predict>-1)
                            --riscv->hash[(pc+i*i)%12281].predict;
                    }
                    break;
                }
            }

            if (pc_context!=jump_choice)
            {
                riscv->ex_out.change=1;
                riscv->ex_out.changeto=the_other;
                ++predict_fail;
            }
            else ++predict_succ;
            riscv->ex_out.res=0;
            riscv->ex_out.ending=0;
        }

        void MA(){}

        void WB(){}
    };
    class S:public Order{
    private:
        int rs2_context;
        int rs1_context;
        int addr;
    public:
        S(int x,Reg* r,int p,Memory* m,Riscv* ri):Order(x,r,p,m,ri){}

        void ID(){
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            rs2=(ins>>20)&31;
            imm=((ins>>7)&31)+(((ins>>25)&127)<<5);
            imm=signed_extend(imm,12);
        }

        void Ex(){
            if (reg[rs1].load_locked()||reg[rs2].load_locked())
            {
                riscv->ex_out.success=0;
                riscv->ex_out.res=0;
                riscv->ex_out.ending=0;
                return;
            }
            else riscv->ex_out.success=1;
            if (rs1==0)
                rs1_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs1_context=reg[rs1].write();
                        break;
                    }
                    case 1:{
                        if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                    case 2:{
                        if (rs1==riscv->ex_buffer.reg[1])
                            rs1_context=riscv->ex_buffer.reg_context[1];
                        else if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                }
            }
            if (rs2==0)
                rs2_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs2_context=reg[rs2].write();
                        break;
                    }
                    case 1:{
                        if (rs2==riscv->ex_buffer.reg[0])
                            rs2_context=riscv->ex_buffer.reg_context[0];
                        else rs2_context=reg[rs2].write();
                        break;
                    }
                    case 2:{
                        if (rs2==riscv->ex_buffer.reg[1])
                            rs2_context=riscv->ex_buffer.reg_context[1];
                        else if (rs2==riscv->ex_buffer.reg[0])
                            rs2_context=riscv->ex_buffer.reg_context[0];
                        else rs2_context=reg[rs2].write();
                        break;
                    }
                }
            }
            addr=rs1_context+imm;
            riscv->ex_out.res=0;
            riscv->ex_out.ending=0;
            if (addr==0x30004)
            {
                riscv->ex_out.res=reg[10].write()&255;
                riscv->ex_out.ending=1;
            }

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

        void WB(){}
    };
    class R:public Order{
    private:
        int rs1_context,rs2_context,rd_context;
    public:
        R(int x,Reg* r,int p,Memory* m,Riscv* ri):Order(x,r,p,m,ri){}

        void ID(){
            func3=(ins>>12)&7;
            rs1=(ins>>15)&31;
            rs2=(ins>>20)&31;
            rd=(ins>>7)&31;
            func7=(ins>>25)&127;
        }

        void Ex(){
            if (reg[rs1].load_locked()||reg[rs2].load_locked())
            {
                riscv->ex_out.success=0;
                riscv->ex_out.res=0;
                riscv->ex_out.ending=0;
                return;
            }
            else riscv->ex_out.success=1;
            if (rs1==0)
                rs1_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs1_context=reg[rs1].write();
                        break;
                    }
                    case 1:{
                        if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                    case 2:{
                        if (rs1==riscv->ex_buffer.reg[1])
                            rs1_context=riscv->ex_buffer.reg_context[1];
                        else if (rs1==riscv->ex_buffer.reg[0])
                            rs1_context=riscv->ex_buffer.reg_context[0];
                        else rs1_context=reg[rs1].write();
                        break;
                    }
                }
            }
            if (rs2==0)
                rs2_context=0;
            else {
                switch (riscv->ex_buffer.count){
                    case 0:{
                        rs2_context=reg[rs2].write();
                        break;
                    }
                    case 1:{
                        if (rs2==riscv->ex_buffer.reg[0])
                            rs2_context=riscv->ex_buffer.reg_context[0];
                        else rs2_context=reg[rs2].write();
                        break;
                    }
                    case 2:{
                        if (rs2==riscv->ex_buffer.reg[1])
                            rs2_context=riscv->ex_buffer.reg_context[1];
                        else if (rs2==riscv->ex_buffer.reg[0])
                            rs2_context=riscv->ex_buffer.reg_context[0];
                        else rs2_context=reg[rs2].write();
                        break;
                    }
                }
            }
            switch (func3){
                case 0:{
                    if (func7)
                    {
                        rd_context=rs1_context-rs2_context;
                    }
                    else {
                        rd_context=rs1_context+rs2_context;
                    }
                    break;
                }
                case 1:{
                    rd_context=rs1_context<<(rs2_context&31);
                    break;
                }
                case 2:{
                    rd_context=(rs1_context<rs2_context)?1:0;
                    break;
                }
                case 3:{
                    rd_context=((unsigned int)rs1_context<(unsigned int)rs2_context)?1:0;
                    break;
                }
                case 4:{
                    rd_context=rs1_context^rs2_context;
                    break;
                }
                case 5: {
                    if (func7)
                        rd_context=rs1_context>>(rs2_context&31);
                    else rd_context=(unsigned int)rs1_context>>(rs2_context&31);
                    break;
                }
                case 6:{
                    rd_context=rs1_context|rs2_context;
                    break;
                }
                case 7:{
                    rd_context=rs1_context&rs2_context;
                    break;
                }
            }

            if (rd!=0)
            {
                riscv->ex_buffer.reg[riscv->ex_buffer.count++]=rd;
                riscv->ex_buffer.reg_context[riscv->ex_buffer.count-1]=rd_context;
            }
            riscv->ex_out.res=0;
            riscv->ex_out.ending=0;
        }

        void MA(){}

        void WB(){
            if (rd==0)
                return;
            reg[rd]=rd_context;
            riscv->ex_buffer.reg_context[0]=riscv->ex_buffer.reg_context[1];
            riscv->ex_buffer.reg_context[1]=0;
            riscv->ex_buffer.reg[0]=riscv->ex_buffer.reg[1];
            riscv->ex_buffer.reg[1]=0;
            if (riscv->ex_buffer.count)
                --riscv->ex_buffer.count;

        }
    };

    struct Ex_out_buffer{
        bool ending=0;
        unsigned int res=0;
        bool success;
        bool change=0;
        int changeto;
        Order* inst=NULL;
        void operator=(int x)
        {
            if (x==0)
            {
                ending=0;
                res=0;
                inst=NULL;
                success=1;
            }
        }
    };
    struct Ex_buffer{
        Order* inst=NULL;
        int reg[2]={0,0};
        int reg_context[2]={0,0};
        int count=0;
    };
    struct ID_buffer{
        int pc=0;
        int ins=0;
        int jump_choice=0;
        int the_other=0;
    };
    ID_buffer id_buffer;
    Ex_out_buffer ex_out;
    Ex_buffer ex_buffer;
    Order *WB_in_inst=NULL,*WB_out_inst=NULL;

    void IF()
    {
        id_buffer.pc=pc.write();
        id_buffer.ins=(memory[pc.write()+3]<<24)+(memory[pc.write()+2]<<16)+(memory[pc.write()+1]<<8)+memory[pc.write()];
        if ((id_buffer.ins&127)==0x63)
        {
            int i;
            for (i=0;i<10000;i++)
            {
                if (!hash[(id_buffer.pc + i * i) % 12281].pc) {
                    hash[(id_buffer.pc + i * i) % 12281].pc = id_buffer.pc;
                    break;
                }
                if (hash[(id_buffer.pc + i * i) % 12281].pc == id_buffer.pc)
                    break;
            }
            if (hash[(id_buffer.pc + i * i) % 12281].predict<=0)
            {
                pc+=4;
                id_buffer.jump_choice=pc.write();
            }
            else {
                pc=hash[(id_buffer.pc + i * i) % 12281].jump;
                id_buffer.jump_choice=hash[(id_buffer.pc + i * i) % 12281].jump;
            }
        }
        else pc+=4;
    }
    void ID()
    {
        if (!id_buffer.ins)
        {
            ex_buffer.inst=NULL;
            return;
        }
        Order *p;
        int a=id_buffer.ins&127;
        switch (a){
            case 0x37:
            case 0x17:p=new U(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
            case 0x6f:p=new J(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
            case 0x67:p=new I(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
            case 0x63:p=new B(id_buffer.ins,reg,id_buffer.pc,&memory,this,id_buffer.jump_choice);break;
            case 0x3:p=new I(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
            case 0x23:p=new S(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
            case 0x13:p=new I(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
            case 0x33:p=new R(id_buffer.ins,reg,id_buffer.pc,&memory,this);break;
        }
        p->ID();
        ex_buffer.inst=p;
    }
    void Ex()
    {
        if (!ex_buffer.inst)
        {
            ex_out=0;
            return ;
        }
        ex_buffer.inst->Ex();
        ex_out.inst=ex_buffer.inst;
    }
    void MA()
    {
        if (ex_out.inst)
            ex_out.inst->MA();
        WB_in_inst=ex_out.inst;
    }
    void WB()
    {
        if (WB_in_inst)
            WB_in_inst->WB();
        WB_out_inst=WB_in_inst;
    }

    void test()
    {
        /*if (reg[10].write()!=before)
        {
            cout<<reg[10].write()<<' '<<count<<' '<<pc.write()<<endl;
            before=reg[10].write();
        }*/
        cout<<count<<"   "<<pc.write()<<' ';
        for (int i=0;i<32;++i)
            cout<<reg[i].write()<<' ';
        cout<<endl;
    }

public:

    void run()
    {
        ex_out.ending=0;
        while (!ex_out.ending)
        {
            //并行********************
            if (count==287569)
                int x=0;
            WB();
            WB_in_inst=NULL;
            MA();
            ex_out.inst=NULL;
            Ex();
            if (ex_out.success)
            {
                if (ex_out.change)
                {
                    ex_buffer.inst=NULL;
                    pc=ex_out.changeto;
                    IF();
                    ex_out.change=0;
                }
                else {
                    ex_buffer.inst=NULL;
                    ID();
                    id_buffer.ins=0;
                    IF();
                }
            }

           //串行**************
           /* IF_inst=IF();
            ID_buffer=ID(IF_inst);
            ex_buffer=Ex(ID_buffer);
            MA_buffer=MA(ex_buffer.inst);
            WB_buffer=WB(MA_buffer);*/
           //***********************
           //test();
            ++count;
            if (WB_out_inst)
                delete WB_out_inst;
        }
        cout<<ex_out.res;
        if (WB_in_inst)
            delete WB_in_inst;
        if (ex_buffer.inst)
            delete ex_buffer.inst;
        if (ex_out.inst)
            delete ex_out.inst;
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
    //char n[20];
    //strcpy(n,
    //"basicopt1.data"
    //"bulgarian.data"
    //"magic.data"
    //"pi.data"
    //"queens.data"
    //"array_test1.data"
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
    //freopen(n, "r", stdin);
    //freopen("answer", "w", stdout);
    //time_t start,ending;
    //start=time(NULL);
    riscv.get_memory();
    riscv.run();
    //ending=time(NULL);
    //cout<<"  time spent  "<<ending-start<<endl;
    //cout<<"prediction success times "<<predict_succ<<" prediction failure times "<<predict_fail<<" success rate "<<(predict_succ*100/(predict_fail+predict_succ))<<'%'<<endl;
    return 0;
}
