#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define Iimage "iimage.bin"
#define Dimage "dimage.bin"
#define ERROR "error_dump.rpt"
#define SNAPSHOT "snapshot.rpt"
#define REPORT "report.rpt"

#define op_func  0x00

#define op_addi  0x08
#define op_lw    0x23
#define op_lh    0x21
#define op_lhu   0x25
#define op_lb    0x20
#define op_lbu   0x24
#define op_sw    0x2B

#define op_sh    0x29
#define op_sb    0x28
#define op_lui   0x0F
#define op_andi  0x0C
#define op_ori   0x0D
#define op_nori  0x0E
#define op_slti  0x0A
#define op_beq   0x04
#define op_bne   0x05

#define op_j     0x02
#define op_jal   0x03

#define op_halt  0x3F

#define func_add  0x20
#define func_sub  0x22
#define func_and  0x24
#define func_or   0x25
#define func_xor  0x26
#define func_nor  0x27
#define func_nand 0x28
#define func_slt  0x2A
#define func_sll  0x00
#define func_srl  0x02
#define func_sra  0x03
#define func_jr   0x08

typedef unsigned int u32;
typedef unsigned char u8;

struct PTE_entry{
    int validBit;
    u32 PPN;
}*PTE;

struct TLB_entry{
    int validBit;
    u32 VPN;
    u32 PPN;
}*TLB;

struct block_entry{
    int valid_bit;
    u32 tag;
} *cache_block;

struct LRU_queue
{
    int queue[1100];
    int length;
} LRU_memory,LRU_TLB;

struct set_entry{
    int index;
    struct LRU_queue LRU_array;
} *cache_set;

struct reslt
{
    int hit;
    int miss;
}PTE_result={0,0},TLB_result={0,0},cache_result={0,0};


void load_iimage();
void load_dimage();
int getSlice(u32,int,int);
int getSignedSlice(u32,int,int);
u32 LMemory(int,int,int);
void SMemory(int,int,u32);


void initial();
void cycle();
u32 retrieveInstr(u32);
void execute_instr(u32);
void printSnapShot(int);

void R_instr(u32);
void ADD(int,int,int);
void SUB(int,int,int);
void AND(int,int,int);
void OR(int,int,int);
void XOR(int,int,int);
void NOR(int,int,int);
void NAND(int,int,int);
void SLT(int,int,int);
void SLL(int,int,int);
void SRL(int,int,int);
void SRA(int,int,int);
void JR(int);

void J(u32);
void JAL(u32);

void I_instr(u32);
void ADDI(int,int,int);
void LW(int,int,int);
void LH(int,int,int);
void LHU(int,int,int);
void HU(int,int,int);
void LB(int,int,int);
void LBU(int,int,int);
void SW(int,int,int);
void SH(int,int,int);
void SB(int,int,int);
void LUI(int,int);
void ANDI(int,int,int);
void ORI(int,int,int);
void NORI(int,int,int);
void SLTI(int,int,int);
void BEQ(int,int,int);
void BNE(int,int,int);

void exam_numOverflow(int,int,int);
int exam_memOverflow(int,int);
int exam_misalign(int,int);
int exam_zeroReg(int);

int fetchDataToMemory(u32);
void push(struct LRU_queue *,int);
int pop(struct LRU_queue *);
int getPow(u32);

u32 checkTLB(u32);
u32 checkPTE(u32);
void checkCache(u32);
void changeCacheValidBit(u32);
void printReport();
//global variable
FILE *snapShot,*error,*report;
int n_cycle=0,halt=0;
u32 reg[32],instr_num=0,mem_num=0;
u32 PC;
u8 D_Memory[2000],I_Memory[2000];

int num_block,num_set;
int PTE_size,TLB_size;
int PPN_MAX;
int PPN_index;
int TLB_index;
u32 *PPNtoVPN,*PPNtoTLBindex;

int memory_size;
int disk_size;
int page_size;

int cache_size;
int block_size;
int n_way;

u32 D_address[1000000];
u32 D_cycle[1000000];
u32 I_address[1000000];
int D_address_length;
int I_address_length;

int command[20];
////////////////////////////////////////////////////////////////////////////
char memory[1024];
char dmemory[1024];
int reg_w[32];
int opcode,rs,rt,rd,shamt,func,immediate;
unsigned int pcAddress,numOfinstruction,numOfdata,instruction;
unsigned int cycleNum=0;
#define reg reg_w
void initImemory()
{
    int i;
    unsigned char buf[4];
    cycleNum=0;
    FILE *fp;
    fp=fopen("error_dump.rpt", "w");
    fclose(fp);
    fp=fopen("snapshot.rpt", "w");
    fclose(fp);
    
    fp=fopen("iimage.bin", "r");
    for(i=0;i<1024;memory[i++]=0);
    for(i=0;i<32;reg[i++]=0);
    fread((void *)buf, (size_t)1, (size_t)4, fp);
    pcAddress = (buf[0] << 24) |   (buf[1] << 16) |  (buf[2] << 8) | buf[3];
    fread(&buf, (size_t)1, (size_t)4, fp);
    numOfinstruction = (buf[0] << 24) |   (buf[1] << 16) |  (buf[2] << 8) | buf[3];
    fread((void *)(memory+pcAddress), (size_t)1, (size_t)numOfinstruction*4, fp);
    fclose(fp);
    fp=fopen("dimage.bin", "r");
    for(i=0;i<1024;dmemory[i++]=0);
    fread((void *)buf, (size_t)1, (size_t)4, fp);
    reg[29] = (buf[0] << 24) |   (buf[1] << 16) |  (buf[2] << 8) | buf[3];
    fread(&buf, (size_t)1, (size_t)4, fp);
    numOfdata = (buf[0] << 24) |   (buf[1] << 16) |  (buf[2] << 8) | buf[3];
    fread((void *)dmemory, (size_t)1, (size_t)numOfdata*4, fp);
    fclose(fp);
}

void printMemOverflow(unsigned int cycle)
{
    FILE *fp;
    fp=fopen("error_dump.rpt", "a");
    fprintf(fp, "In cycle %d: Address Overflow\n",cycle+1);
    fclose(fp);
}

void printNoerror(unsigned int cycle)
{
    FILE *fp;
    fp=fopen("error_dump.rpt", "a");
    fprintf(fp, "In cycle %d: Number Overflow\n",cycle+1);
    fclose(fp);
}

void print0error(unsigned int cycle)
{
    FILE *fp;
    fp=fopen("error_dump.rpt", "a");
    fprintf(fp, "In cycle %d: Write $0 Error\n",cycle+1);
    fclose(fp);
}

void printMisAligned(unsigned int cycle)
{
    FILE *fp;
    fp=fopen("error_dump.rpt", "a");
    fprintf(fp, "In cycle %d: Misalignment Error\n",cycle+1);
    fclose(fp);
}
unsigned int getInstruction(int address)
{
    /*
     if(address<0||address>1020)
     {
     printMemOverflow(cycleNum);
     }*/
    return (memory[address]<<24)+((memory[address+1]<<16) & 0xff0000)+((memory[address+2]<<8) & 0xff00)+(memory[address+3] & 0xff);
}

void putWord(int address,unsigned int value)
{
    int status=0;
    if(address<0||address>1020)
    {
        printMemOverflow(cycleNum);
        status=1;
    }
    if(address%4!=0){
        printMisAligned(cycleNum);
        status=1;
    }
    if(status==1)
    {
        exit(1);
    }
    dmemory[address]=(char)(value>>24);//最高位
    dmemory[address+1]=(char)((value & 0xff0000)>>16);
    dmemory[address+2]=(char)((value & 0xff00)>>8);
    dmemory[address+3]=(char)(value & 0xff);
    
}


unsigned int getWord(int address)
{
    int status=0;
    if(address<0||address>1020)
    {
        printMemOverflow(cycleNum);
        status=1;
    }
    if(address%4!=0){
        printMisAligned(cycleNum);
        status=1;
    }
    if(status==1)
    {
        exit(1);
    }
    return (dmemory[address]<<24)+((dmemory[address+1]<<16) & 0xff0000)+((dmemory[address+2]<<8) & 0xff00)+(dmemory[address+3] & 0xff);
}

void put2Byte(int address,int value)
{
    int status=0;
    if(address<0||address>1022)
    {
        printMemOverflow(cycleNum);
        status=1;
    }
    if(address%2!=0){
        printMisAligned(cycleNum);
        status=1;
    }
    if(status==1)
    {
        exit(1);
    }
    dmemory[address]=(char)((value<<16)>>24);//最高位，这里做法可以精简
    dmemory[address+1]=(char)((value<<24)>>24);
    
}

int get2Byte(int address)
{
    int status=0;
    if(address<0||address>1022)
    {
        printMemOverflow(cycleNum);
        status=1;
    }
    if(address%2!=0){
        printMisAligned(cycleNum);
        status=1;
    }
    if(status==1)
    {
        exit(1);
    }
    int rv=((dmemory[address]<<8) & 0xff00)+(dmemory[address+1] & 0xff);
    return (rv<<16)>>16;  //左移加右移可以有符号
}

int get2Byteu(int address)
{
    int status=0;
    if(address<0||address>1022)
    {
        printMemOverflow(cycleNum);
        status=1;
    }
    if(address%2!=0){
        printMisAligned(cycleNum);
        status=1;
    }
    if(status==1)
    {
        exit(1);
    }
    return ((dmemory[address]<<8) & 0xff00)+(dmemory[address+1] & 0xff) & 0x0000ffff;  //用0x0000ffff消除符号
}


void putByte( int address, int value )
{
    if ((address < 0) || (address > 1023))
    {
        printMemOverflow(cycleNum);
        exit(1);
    }
    dmemory[address] = (char)(value);   //经测试，直接截断
}

int getByte (int address)
{
    int n ;
    if ((address < 0) || (address > 1023))
    {
        printMemOverflow(cycleNum);
        exit(1);
    }
    
    n = dmemory[address] ;//有符号
    return (n<<24)>>24 ;
}

unsigned int getByteu (int address)
{
    unsigned int n ;
    if ((address < 0) || (address > 1023))
    {
        printMemOverflow(cycleNum);
        exit(1);
    }
    
    n = (unsigned int)dmemory[address] &0x000000ff;//无符号
    return n ;
}

void regSet(int address,int value)
{
    if(address==0){
        print0error(cycleNum);
        reg[0]=0;
        return;
    }
    reg[address]=value;
}

void regSetNoWarn(int address,int value)
{
    if(address==0){
        reg[0]=0;
        return;
    }
    reg[address]=value;
}

int addNum(int addend1,int addend2)
{
    int z=addend1+addend2;
    if((addend1>=0&&addend2>=0&&z<0)||(addend1<0&&addend2<0&&z>=0)){//溢出
        printNoerror(cycleNum);
    }
    return z;
}

void classify(int ins)
{
    opcode=(ins>>26 & 0x3f);//将数据存入段间寄存器
    rs=(ins>>21 & 0x1f);//5bit
    rt=(ins>>16 & 0x1f);//5bit
    rd=(ins>>11 & 0x1f);//5bit
    shamt=(ins>>6 & 0x1f);//5bit
    func=(ins & 0x3f);//6bit
    immediate=(ins<<16)>>16;//16bit immediate带符号
}

void exec()
{
    instruction=getInstruction(pcAddress);
    pcAddress+=4;
    classify(instruction);
    switch (opcode) {
        case 0://R-Format
            switch (func) {
                case 0x20:
                    if(rd==0){
                        print0error(cycleNum);
                    }
                    regSetNoWarn(rd, addNum(reg[rs],reg[rt]));
                    break;
                case 0x22:
                    if(rd==0){
                        print0error(cycleNum);
                    }
                    regSetNoWarn(rd, addNum(reg[rs],-reg[rt]));
                    break;
                case 0x24:
                    regSet(rd, reg[rs] & reg[rt]);
                    break;
                case 0x25:
                    regSet(rd, reg[rs]|reg[rt]);
                    break;
                case 0x26:
                    regSet(rd, reg[rs]^reg[rt]);
                    break;
                case 0x27:
                    regSet(rd, ~(reg[rs]|reg[rt]));
                    break;
                case 0x28:
                    regSet(rd, ~(reg[rs]&reg[rt]));
                    break;
                case 0x2A:
                    if(reg[rs]<reg[rt]){
                        regSet(rd, 1);
                    }else{
                        regSet(rd, 0);
                    }
                    break;
                case 0x00:
                    if(rd==0&&rt==0&&shamt==0){
                        reg[0]=0;
                    }else{
                        regSet(rd, reg[rt]<<shamt);
                    }
                    break;
                case 0x02:
                    regSet(rd, ((unsigned int)reg[rt])>>shamt);
                    break;
                case 0x03:
                    regSet(rd, reg[rt]>>shamt);
                    break;
                case 0x08:
                    pcAddress=reg[rs];
                    break;
                default:
                    break;
            }
            break;
        case 0x08:
            if(rt==0){
                print0error(cycleNum);
            }
            regSetNoWarn(rt, addNum(reg[rs],immediate));
            break;
        case 0x23:
            if(rt==0){
                print0error(cycleNum);
            }
            regSetNoWarn(rt, getWord(addNum(reg[rs],immediate)));
            break;
        case 0x21:
            if(rt==0){
                print0error(cycleNum);
            }
            regSetNoWarn(rt, get2Byte(addNum(reg[rs],immediate)));
            break;
        case 0x25:
            //lhu
            if(rt==0){
                print0error(cycleNum);
            }
            regSetNoWarn(rt, get2Byteu(addNum(reg[rs],immediate)));
            break;
        case 0x20:
            if(rt==0){
                print0error(cycleNum);
            }
            regSetNoWarn(rt, getByte(addNum(reg[rs],immediate)));
            break;
        case 0x24:
            //lbu
            if(rt==0){
                print0error(cycleNum);
            }
            regSetNoWarn(rt, getByteu(addNum(reg[rs],immediate)));
            break;
        case 0x2B:
            putWord(addNum(reg[rs],immediate), reg[rt]);
            break;
        case 0x29:
            put2Byte(addNum(reg[rs],immediate), reg[rt]);
            break;
        case 0x28:
            putByte(addNum(reg[rs],immediate), reg[rt]);
            break;
        case 0x0F:
            regSet(rt, immediate<<16);//sll右边会自动补0，不存在符号问题，把高16位存入
            break;
        case 0x0C:
            //这里修改
            regSet(rt, reg[rs] & (immediate & 0x0000FFFF));
            break;
        case 0x0D:
            regSet(rt, reg[rs] | (immediate & 0x0000FFFF));
            break;
        case 0x0E:
            regSet(rt, ~(reg[rs] | (immediate & 0x0000FFFF)));
            break;
        case 0x0A:
            if (reg[rs]<immediate) {
                regSet(rt, 1);
            }else{
                regSet(rt, 0);
            }
            break;
        case 0x04:
            if(reg[rs]==reg[rt]){
                pcAddress=addNum(pcAddress, 4*immediate);
            }
            break;
        case 0x05:
            if(reg[rs]!=reg[rt]){
                pcAddress=addNum(pcAddress, 4*immediate);
            }
            break;
        case 0x02:
            pcAddress=((pcAddress) & 0xf0000000) | ((immediate & 0x03ffffff)*4);
            break;
        case 0x03:
            regSet(31, pcAddress);
            pcAddress=((pcAddress) & 0xf0000000) | ((immediate & 0x03ffffff)*4);
            break;
        case 0x3F:
            exit(1);
        default:
            break;
    }
    cycleNum++;
    
}

void printReg()
{
    int i;
    FILE *fp;
    fp=fopen("snapshot.rpt", "a");
    fprintf(fp, "%s%d\n","cycle ",cycleNum);
    
    for (i=0; i<32; ++i) {
        fprintf(fp, "%s%02d%s%08X\n","$",i,": 0x",reg[i]);
    }
    fprintf(fp, "%s%08X\n\n\n","PC: 0x",pcAddress);
    //    fprintf(fp, "%s%08X\n","INS: 0x",instruction);
    fclose(fp);
}

void s()
{
    
    initImemory();
    while (1) {
        printReg();
        exec();
    }
    
}
#undef reg

///////////////////////////////////////////////////////////////////////////

int main (int argc, char* argv[])
{
    
    int i;
    if(argc==11)
    {
        for(i=0;i<argc;i++)
        {
            command[i]=atoi(argv[i]);
        }
    }
    report=fopen(REPORT,"w");
    initial();
    load_iimage();
    load_dimage();
    printSnapShot(n_cycle++);
    while(halt==0){
        if(n_cycle==38){
            printf("1");
        }
        cycle();
    }
    printReport();
    s();
    return 0;
}


void initial()
{
    int i=0;
    PC=0;
    D_address_length=0;
    I_address_length=0;
    for (i=0;i<32;i++)
        reg[i]=0;
    for (i=0;i<2000;i++)
    {
        I_Memory[i]=0;
        D_Memory[i]=0;
    }
}

void cycle()
{
    exam_memOverflow(PC,1);
    exam_misalign(PC,4);
    if (halt==1)
        return;
    u32 instruction=retrieveInstr(PC);
    //printf("excuting [%d] 0x%08x ...\n",n_cycle,instruction);
    PC=PC+4;
    execute_instr(instruction);
    
    reg[0]=0;
    if (halt!=1)
        printSnapShot(n_cycle++);
}

u32 retrieveInstr(u32 PC)
{
    int i;
    u32 instrction=0;
    for (i=3;i>=0;i--)
    {
        instrction=instrction<<8;
        instrction=instrction|I_Memory[PC+i];
    }
    if (n_cycle==19)
        printf("(%d) PC = %d, 0x%08x\n",n_cycle,PC,instrction);
    return instrction;
}

void execute_instr(u32 instruction)
{
    int opcode=getSlice(instruction,31,26);
    
    if (opcode==0x00)
        R_instr(instruction);
    else if(opcode==0x02)
        J(getSlice(instruction,25,0));
    else if (opcode==0x03)
        JAL(getSlice(instruction,25,0));
    else if (opcode==0x3f)
    {
        halt=1;
        return;
    }
    else
        I_instr(instruction);
}

void R_instr(u32 instrction)
{
    int func=getSlice(instrction,5,0);
    int rs_index=getSlice(instrction,25,21);
    int rt_index=getSlice(instrction,20,16);
    int rd_index=getSlice(instrction,15,11);
    int shamt = getSlice(instrction,10,6);
    
    if (func==func_add)
        ADD(rs_index,rt_index,rd_index);
    else if (func==func_sub)
        SUB(rs_index,rt_index,rd_index);
    else if (func==func_and)
        AND(rs_index,rt_index,rd_index);
    else if (func==func_or)
        OR(rs_index,rt_index,rd_index);
    else if (func==func_xor)
        XOR(rs_index,rt_index,rd_index);
    else if (func==func_nor)
        NOR(rs_index,rt_index,rd_index);
    else if (func==func_nand)
        NAND(rs_index,rt_index,rd_index);
    else if (func==func_slt)
        SLT(rs_index,rt_index,rd_index);
    else if (func==func_sll)
        SLL(rt_index,rd_index,shamt);
    else if (func==func_srl)
        SRL(rt_index,rd_index,shamt);
    else if (func==func_sra)
        SRA(rt_index,rd_index,shamt);
    else if (func==func_jr)
        JR(rs_index);
    else
        printf("0x%08x is an undefined instruction!\n",instrction);
    
}

void I_instr(u32 instrction)
{
    int immediate=getSlice(instrction,15,0);
    int signed_imm=getSignedSlice(instrction,15,0);
    int rs_index=getSlice(instrction,25,21);
    int rt_index=getSlice(instrction,20,16);
    int opcode=getSlice(instrction,31,26);
    
    if (opcode==op_addi)
        ADDI(rs_index,rt_index,signed_imm);
    else if(opcode==op_lw)
        LW(rs_index,rt_index,signed_imm);
    else if(opcode==op_lh)
        LH(rs_index,rt_index,signed_imm);
    else if(opcode==op_lhu)
        LHU(rs_index,rt_index,signed_imm);
    else if(opcode==op_lb)
        LB(rs_index,rt_index,signed_imm);
    else if(opcode==op_lbu)
        LBU(rs_index,rt_index,signed_imm);
    else if(opcode==op_sw)
        SW(rs_index,rt_index,signed_imm);
    else if(opcode==op_sh)
        SH(rs_index,rt_index,signed_imm);
    else if(opcode==op_sb)
        SB(rs_index,rt_index,signed_imm);
    else if(opcode==op_lui)
        LUI(rt_index,immediate);
    else if(opcode==op_andi)
        ANDI(rs_index,rt_index,immediate);
    else if(opcode==op_ori)
        ORI(rs_index,rt_index,immediate);
    else if(opcode==op_nori)
        NORI(rs_index,rt_index,immediate);
    else if(opcode==op_slti)
        SLTI(rs_index,rt_index,signed_imm);
    else if(opcode==op_beq)
        BEQ(rs_index,rt_index,signed_imm);
    else if(opcode==op_bne)
        BNE(rs_index,rt_index,signed_imm);
}

void ADD(int rs_index,int rt_index,int rd_index)
{
    int zero_reg = exam_zeroReg(rd_index);
    exam_numOverflow(reg[rs_index],reg[rt_index],reg[rs_index]+reg[rt_index]);
    if (zero_reg==0)
        reg[rd_index]=reg[rs_index]+reg[rt_index];
}

void SUB(int rs_index,int rt_index,int rd_index)
{
    int zero_reg = exam_zeroReg(rd_index);
    
    if (reg[rt_index]!=0&&(unsigned int)(~reg[rt_index]+1)==(unsigned int)reg[rt_index])
    {
        fprintf(error,"Number overflow in cycle: %d\n",n_cycle);
        if (zero_reg==0)
            reg[rd_index]=reg[rs_index]+(~reg[rt_index]+1);
        //printf("0x%08x, 0x%08x, 0x%08x\n",reg[rs_index],(~reg[rt_index]+1),reg[rd_index]);
    }
    else
    {
        exam_numOverflow(reg[rs_index],(~reg[rt_index]+1),reg[rs_index]+(~reg[rt_index]+1));
        if (zero_reg==0)
            reg[rd_index]=reg[rs_index]+(~reg[rt_index]+1);
    }
}

void AND(int rs_index,int rt_index,int rd_index)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    reg[rd_index]=reg[rs_index]&reg[rt_index];
}

void OR(int rs_index,int rt_index,int rd_index)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    reg[rd_index]=reg[rs_index]|reg[rt_index];
}

void XOR(int rs_index,int rt_index,int rd_index)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    reg[rd_index]=reg[rs_index]^reg[rt_index];
}

void NOR(int rs_index,int rt_index,int rd_index)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    reg[rd_index]=~(reg[rs_index]|reg[rt_index]);
}

void NAND(int rs_index,int rt_index,int rd_index)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    reg[rd_index]=~(reg[rs_index]&reg[rt_index]);
}

void SLT(int rs_index,int rt_index,int rd_index)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    //signed
    if ((signed int)reg[rs_index]<(signed int)reg[rt_index])
        reg[rd_index]=1;
    else
        reg[rd_index]=0;
}

void SLL(int rt_index,int rd_index,int shamt)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    if (shamt==32)
        reg[rd_index]=0x00000000;
    else if (shamt==0)
        reg[rd_index]=reg[rt_index];
    else
        reg[rd_index]=reg[rt_index]<<shamt;
    
}

void SRL(int rt_index,int rd_index,int shamt)
{
    if (exam_zeroReg(rd_index)==1)
        return;
    if (shamt==32)
        reg[rd_index]=0x00000000;
    else if (shamt==0)
        reg[rd_index]=reg[rt_index];
    else
        reg[rd_index]=reg[rt_index]>>shamt;
}

void SRA(int rt_index,int rd_index,int shamt)
{
    int sign=0;
    if (exam_zeroReg(rd_index)==1)
        return;
    if (shamt==32)
        reg[rd_index]=0x00000000;
    else if (shamt==0)
        reg[rd_index]=reg[rt_index];
    else{
        if (reg[rt_index]>>31==1)
            sign=1;
        reg[rd_index]=reg[rt_index]>>shamt;
        if (sign&&shamt!=0)
            reg[rd_index]=reg[rd_index]|(unsigned int)(0xffffffff<<(32-shamt));
    }
}

void JR(int rs_index)
{
    PC=reg[rs_index];
}

void J(u32 address)
{
    PC=(getSlice(PC,31,28)<<26)|(address*4);
}

void JAL(u32 address)
{
    reg[31]=PC;
    PC=(getSlice(PC,31,28)<<28)|(address*4);
}

void ADDI(int rs_index,int rt_index,int immediate)
{
    int zero_reg=exam_zeroReg(rt_index);
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    if (zero_reg==0)
        reg[rt_index]=reg[rs_index]+immediate;
}

void LW(int rs_index,int rt_index,int immediate)
{
    //printf("LW $%d = %d($%d)\n",rt_index,immediate,rs_index);
    exam_zeroReg(rt_index);
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,4);
    exam_misalign(reg[rs_index]+immediate,4);
    
    if (halt==0)
        reg[rt_index]=LMemory(reg[rs_index]+immediate,4,0);
}

void LH(int rs_index,int rt_index,int immediate)
{
    exam_zeroReg(rt_index);
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,2);
    exam_misalign(reg[rs_index]+immediate,2);
    
    if (halt==0)
        reg[rt_index]=LMemory(reg[rs_index]+immediate,2,1);
}

void LHU(int rs_index,int rt_index,int immediate)
{
    exam_zeroReg(rt_index);
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,2);
    exam_misalign(reg[rs_index]+immediate,2);
    
    if (halt==0)
        reg[rt_index]=LMemory(reg[rs_index]+immediate,2,0);
}

void LB(int rs_index,int rt_index,int immediate)
{
    exam_zeroReg(rt_index);
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,1);
    
    if (halt==0)
        reg[rt_index]=LMemory(reg[rs_index]+immediate,1,1);
}

void LBU(int rs_index,int rt_index,int immediate)
{
    exam_zeroReg(rt_index);
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,1);
    
    if (halt==0)
        reg[rt_index]=LMemory(reg[rs_index]+immediate,1,0);
}

void SW(int rs_index,int rt_index,int immediate)
{
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,4);
    exam_misalign(reg[rs_index]+immediate,4);
    
    if (halt==0)
        SMemory(reg[rs_index]+immediate,4,reg[rt_index]);
    
}

void SH(int rs_index,int rt_index,int immediate)
{
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,2);
    exam_misalign(reg[rs_index]+immediate,2);
    
    if (halt==0)
        SMemory(reg[rs_index]+immediate,2,reg[rt_index]);
    
}

void SB(int rs_index,int rt_index,int immediate)
{
    exam_numOverflow(reg[rs_index],immediate,reg[rs_index]+immediate);
    exam_memOverflow(reg[rs_index]+immediate,1);
    
    if (halt==0)
        SMemory(reg[rs_index]+immediate,1,reg[rt_index]);
}

void LUI(int rt_index,int immediate)
{
    if (exam_zeroReg(rt_index)==1)
        return;
    reg[rt_index]=immediate<<16;
}

void ANDI(int rs_index,int rt_index,int immediate)
{
    if (exam_zeroReg(rt_index)==1)
        return;
    reg[rt_index]=reg[rs_index]&immediate;
}

void ORI(int rs_index,int rt_index,int immediate)
{
    if (exam_zeroReg(rt_index)==1)
        return;
    reg[rt_index]=reg[rs_index]|immediate;
}

void NORI(int rs_index,int rt_index,int immediate)
{
    if (exam_zeroReg(rt_index)==1)
        return;
    reg[rt_index]=~(reg[rs_index]|immediate);
}

void SLTI(int rs_index,int rt_index,int immediate)
{
    if (exam_zeroReg(rt_index)==1)
        return;
    reg[rt_index]=((signed int)reg[rs_index]<(signed int)immediate)?1:0;
}

void BEQ(int rs_index,int rt_index,int immediate)
{
    if(reg[rt_index]==reg[rs_index])
    {
        exam_numOverflow(PC,(immediate<<2),PC+4*immediate);
        PC=PC+4*immediate;
    }
}

void BNE(int rs_index,int rt_index,int immediate)
{
    if(reg[rt_index]!=reg[rs_index])
    {
        exam_numOverflow(PC,(immediate<<2),PC+4*immediate);
        PC=PC+4*immediate;
    }
}

int getSlice(u32 instrction,int from,int to) //unsigned slice
{
    return (instrction<<(31-from))>>(32-(from-to+1));
}

int getSignedSlice(u32 instrction,int from,int to) // signed slice
{
    int sign=(instrction<<(31-from))>>31;
    int slice=(instrction<<(31-from))>>(32-(from-to+1));
    
    if (sign==1)
    {
        slice=slice|(0xffffffff<<(from-to+1));
    }
    
    return slice;
}

u32 LMemory(int memoryLocation,int byteNum,int sign)
{
    int temp=0,i;
    int MSB;
    
    //fprintf(datarpt,"%d\n",memoryLocation);
    D_address[D_address_length++]=memoryLocation;
    /*if (exam_memOverflow(memoryLocation,byteNum)==1)
     return 0;*/
    
    MSB=D_Memory[memoryLocation+byteNum-1]>>7;
    
    for (i=byteNum-1;i>=0;i--)
    {
        if (n_cycle==19)
            printf("mem[%d] = 0x%02x\n",memoryLocation+i,D_Memory[memoryLocation+i]);
        temp=(temp<<8);
        temp=temp|D_Memory[memoryLocation+i];
    }
    
    if (sign==1&&MSB==1&&byteNum!=4)
    {
        temp=temp|(0xffffffff<<(8*byteNum));
    }
    //printf("MEM[0x%08x] = 0x%08x\n",memoryLocation,temp);
    return temp;
}

void SMemory(int memoryLocation,int byteNum,u32 data)
{
    int i;
    //fprintf(datarpt,"%d\n",memoryLocation);
    D_address[D_address_length++]=memoryLocation;
    /*if (exam_memOverflow(memoryLocation,byteNum)==1)
     return;*/
    
    for(i=0;i<byteNum;i++)
    {
        printf("store to mem[%d]\n",memoryLocation+i);
        D_Memory[memoryLocation+i]=(u8)(data<<24>>24);
        data=data>>8;
    }
}

void printSnapShot(int n_cycle)
{
    int i=0;
    I_address[I_address_length++]=PC;
}

int exam_zeroReg(int reg_index)
{
    if (reg_index==0)
    {
        reg[0]=0;
        fprintf(error,"Write $0 error in cycle: %d\n",n_cycle);
        return 1;
    }
    else
        return 0;
}

int exam_misalign(int test,int byte)
{
    if (test%byte!=0)
    {
        fprintf(error,"Misalignment error in cycle: %d\n",n_cycle);
        halt=1;
        return 1;
    }
    else
        return 0;
}

void exam_numOverflow(int a,int b,int result)
{
    if (a>>31==b>>31)
        if (a>>31!=result>>31)
        {
            fprintf(error,"Number overflow in cycle: %d\n",n_cycle);
        }
}

int  exam_memOverflow(int index,int length)
{
    int i;
    
    for (i=0;i<length;i++)
    {
        if ((index+i)<0||(index+i)>1023)
        {
            fprintf(error,"Address overflow in cycle: %d\n",n_cycle);
            halt=1;
            return 1;
        }
    }
    
    return 0;
}

void load_iimage()
{
    FILE *fp;
    int n=0;
    u32 sum;
    int n_instr=0;
    int i;
    int pc_done=0;
    u8 buff[4];
    
    fp = fopen(Iimage, "rb");
    if (!fp)
    {
        halt=1;
        printf(Iimage" not found.\n");
        return;
    }
    while(fread(buff, sizeof(char),4, fp))
    {
        sum=0;
        for (i=0; i<=3;i++)
        {
            sum=sum<<8;
            sum=sum|buff[i];
        }
        if (pc_done==0)
        {
            PC=sum;
            pc_done=1;
        }
        else if (instr_num==0)
        {
            instr_num=sum;
        }
        else
        {
            instr_num--;
            for (i=3; i>=0;i--)
            {
                I_Memory[PC+n_instr++]=buff[i];
            }
            if (instr_num<=0)
                break;
        }
    }
}

void load_dimage()
{
    FILE *fp;
    int n=0;
    u32 sum;
    int n_mem=0;
    int i;
    int sp_done=0;
    u8 buff[4];
    
    fp = fopen(Dimage, "rb");
    if (!fp)
    {
        halt=1;
        printf(Dimage" not found.\n");
        return;
    }
    while(fread(buff, sizeof(char),4, fp))
    {
        sum=0;
        for (i=0; i<=3;i++)
        {
            sum=sum<<8;
            sum=sum|buff[i];
        }
        if (sp_done==0)
        {
            reg[29]=sum;
            sp_done=1;
        }
        else if (mem_num==0)
        {
            mem_num=sum;
        }
        else
        {
            mem_num--;
            for (i=3; i>=0;i--)
            {
                D_Memory[n_mem++]=buff[i];
            }
            if(mem_num<=0)
                break;
            
        }
    }
    printf("toatal %d data\n",n_mem);
}

void printReport()
{
    int count;
    int tmp;
    int ICache_hits, ICache_misses,
    DCache_hits, DCache_misses,
    ITLB_hits, ITLB_misses,
    DTLB_hits, DTLB_misses,
    IPageTable_hits, IPageTable_misses,
    DPageTable_hits, DPageTable_misses;
    for(count=0;count<2;count++)
    {
        if(count==0)
        {
            //I ≥WÆÊ
            if(command[1]==0)memory_size=64;else memory_size=(command[1]);
            disk_size=1024;
            if(command[3]==0)page_size=8;else page_size=(command[3]);
            if(command[5]==0)cache_size=16;else cache_size=(command[5]);
            if(command[6]==0)block_size=4;else block_size=(command[6]);
            if(command[7]==0)n_way=4;else n_way=(command[7]);
            
            /*memory_size=32;
             disk_size=1024;
             page_size=16;
             cache_size=16;
             block_size=4;
             n_way=4;*/
            printf("I_memory_size = %d\n",memory_size);
            printf("I_disk_size = %d\n",disk_size);
            printf("I_page_size = %d\n",page_size);
            printf("I_cache_size = %d\n",cache_size);
            printf("I_block_size = %d\n",block_size);
            printf("I_n_way = %d\n",n_way);
        }
        else
        {
            if(command[2]==0)memory_size=32;else memory_size=(command[2]);
            disk_size=1024;
            if(command[4]==0)page_size=16;else page_size=(command[4]);
            if(command[8]==0)cache_size=16;else cache_size=(command[8]);
            if(command[9]==0)block_size=4;else block_size=(command[9]);
            if(command[10]==0)n_way=1;else n_way=(command[10]);
            /*memory_size=32;
             disk_size=1024;
             page_size=16;
             cache_size=16;
             block_size=4;
             n_way=1;*/
            
            printf("D_memory_size = %d\n",memory_size);
            printf("D_disk_size = %d\n",disk_size);
            printf("D_page_size = %d\n",page_size);
            printf("D_cache_size = %d\n",cache_size);
            printf("D_block_size = %d\n",block_size);
            printf("D_n_way = %d\n",n_way);
        }
        int i;
        
        PTE_size=disk_size/page_size;
        TLB_size=PTE_size/4;
        PPN_MAX=memory_size/page_size;
        PPN_index=0;
        TLB_index=0;
        
        num_block=cache_size/block_size;
        num_set=num_block/n_way;
        
        PTE = malloc(sizeof(struct PTE_entry)*PTE_size);
        TLB = malloc(sizeof(struct TLB_entry)*TLB_size);
        PPNtoTLBindex= malloc(sizeof(u32)*TLB_size);
        PPNtoVPN=malloc(sizeof(u32)*PPN_MAX);
        memset(PTE,0,sizeof(struct PTE_entry)*PTE_size);
        memset(TLB,0,sizeof(struct TLB_entry)*TLB_size);
        memset(PPNtoTLBindex,0,sizeof(u32)*TLB_size);
        memset(PPNtoVPN,0,sizeof(u32)*PPN_MAX);
        
        cache_block=malloc(sizeof(struct block_entry)*num_block);
        cache_set=malloc(sizeof(struct set_entry)*num_set);
        memset (cache_block,0,sizeof(struct block_entry)*num_block);
        memset (cache_set,0,sizeof(struct set_entry)*num_set);
        
        PTE_result.hit = 0;
        PTE_result.miss = 0;
        TLB_result.hit = 0;
        TLB_result.miss = 0;
        cache_result.hit = 0;
        cache_result.miss = 0;
        
        memset (&LRU_memory,0,sizeof(struct LRU_queue));
        memset (&LRU_TLB,0,sizeof(struct LRU_queue));
        
        if(count==0)
        {
            for (i=0;i<I_address_length;i++)
            {
                tmp=checkTLB(I_address[i]);
                checkCache(tmp);
            }
            ICache_hits = cache_result.hit;
            ICache_misses = cache_result.miss;
            ITLB_hits = TLB_result.hit;
            ITLB_misses = TLB_result.miss;
            IPageTable_hits = PTE_result.hit;
            IPageTable_misses = PTE_result.miss;
        }
        else
        {
            for (i=0;i<D_address_length;i++)
            {
                tmp=checkTLB(D_address[i]);
                checkCache(tmp);
            }
            DCache_hits = cache_result.hit;
            DCache_misses = cache_result.miss;
            DTLB_hits = TLB_result.hit;
            DTLB_misses = TLB_result.miss;
            DPageTable_hits = PTE_result.hit;
            DPageTable_misses = PTE_result.miss;
        }
    }
    
    fprintf(report,"ICache :\n");
    fprintf(report,"# hits: %d\n",ICache_hits);
    fprintf(report,"# misses: %d\n\n",ICache_misses);
    
    fprintf(report,"DCache :\n");
    fprintf(report,"# hits: %d\n",DCache_hits);
    fprintf(report,"# misses: %d\n\n",DCache_misses);
    
    fprintf(report,"ITLB :\n");
    fprintf(report,"# hits: %d\n",ITLB_hits);
    fprintf(report,"# misses: %d\n\n",ITLB_misses);
    
    fprintf(report,"DTLB :\n");
    fprintf(report,"# hits: %d\n",DTLB_hits);
    fprintf(report,"# misses: %d\n\n",DTLB_misses);
    
    fprintf(report,"IPageTable :\n");
    fprintf(report,"# hits: %d\n",IPageTable_hits);
    fprintf(report,"# misses: %d\n\n",IPageTable_misses);
    
    fprintf(report,"DPageTable :\n");
    fprintf(report,"# hits: %d\n",DPageTable_hits);
    fprintf(report,"# misses: %d\n\n",DPageTable_misses);
    
}

void checkCache(u32 p_add)
{
    u32 tag_index = p_add/block_size;
    u32 tag= tag_index/num_set;
    u32 index = tag_index%num_set;
    int hit=0;
    int i;
    int replace_index;
    
    for (i=0;i<n_way;i++)
        if (cache_block[index*n_way+i].valid_bit==1&&cache_block[index*n_way+i].tag==tag)
        {
            hit=1;
            break;
        }
    
    if (hit==1)
    {
        cache_result.hit++;
        push(&cache_set[index].LRU_array,i);
    }
    else
    {
        cache_result.miss++;
        if (cache_set[index].index<n_way)
        {
            cache_block[index*n_way+cache_set[index].index].valid_bit=1;
            cache_block[index*n_way+cache_set[index].index].tag=tag;
            push(&cache_set[index].LRU_array,cache_set[index].index);
            cache_set[index].index++;
        }
        else
        {
            //LRU
            replace_index=pop(&cache_set[index].LRU_array);
            cache_block[index*n_way+replace_index].valid_bit=1;
            cache_block[index*n_way+replace_index].tag=tag;
            push(&cache_set[index].LRU_array,replace_index);
        }
    }
    
}

void changeCacheValidBit(u32 p_add)
{
    //printf("\n>>check if [%d] is in Cache\n\n",p_add);
    
    u32 tag_index = p_add/block_size;
    u32 tag= tag_index/num_set;
    u32 index = tag_index%num_set;
    int i=0;
    
    for (i=0;i<n_way;i++)
        if (cache_block[index*n_way+i].valid_bit==1&&cache_block[index*n_way+i].tag==tag)
        {
            cache_block[index*n_way+i].valid_bit=0;
            break;
        }
}

u32 checkTLB(u32 address)
{
    
    int offset_bit=getPow(page_size);
    u32 VPN=address>>offset_bit;
    u32 PPN;
    int i;
    int index;
    int hit=0;
    for (i=0;i<TLB_index;i++)
    {
        if (TLB[i].validBit==1&&TLB[i].VPN==VPN)
        {
            PPN=TLB[i].PPN;
            hit=1;
            break;
        }
    }
    
    if (hit==1)
    {
        //printf("  [ TLB hit] ");
        PPN=TLB[i].PPN;
        push(&LRU_TLB,i);
        TLB_result.hit++;
    }
    else
    {
        //printf("  [TLB miss] ");
        PPN = checkPTE(address);
        /*for (i=0;i<TLB_index;i++)
         if (TLB[i].PPN==PPN)
         TLB[i].validBit=0;*/
        if (TLB[PPNtoTLBindex[PPN]].PPN==PPN)
            TLB[PPNtoTLBindex[PPN]].validBit=0;
        
        if (TLB_index<TLB_size)
        {
            PPNtoTLBindex[PPN]=TLB_index;
            TLB[TLB_index].validBit=1;
            TLB[TLB_index].VPN=VPN;
            TLB[TLB_index].PPN=PPN;
            push(&LRU_TLB,TLB_index);
            TLB_index++;
        }
        else
        {
            //LRU
            index=pop(&LRU_TLB);
            PPNtoTLBindex[PPN]=index;
            push(&LRU_TLB,index);
            TLB[index].validBit=1;
            TLB[index].VPN=VPN;
            TLB[index].PPN=PPN;
        }
        TLB_result.miss++;
    }
    //printf("PPN = %d,0x%08X\n",(PPN),(address&(~(0xFFFFFFFF<<offset_bit))));
    return (PPN<<offset_bit)|(address&(~(0xFFFFFFFF<<getPow(page_size))));
}

u32 checkPTE(u32 address) //return PPN
{
    
    u32 VPN=address>>(getPow(page_size));
    
    //printf("[index/size] = [%u/%u]\n",VPN,PTE_size);
    u32 PPN;
    if (PTE[VPN].validBit==0) //PTE miss
    {
        //printf("  [PTE miss] ");
        PTE[VPN].validBit=1;
        PPN=fetchDataToMemory(address); /**if LRU, change one valid bit to zero*/
        PTE[VPN].PPN=PPN;
        PPNtoVPN[PPN]=VPN;
        /**fetch data to cache
         *
         *
         *
         */
        PTE_result.miss++;
    }
    else //PTE hit
    {
        //printf("  [PTE  hit] ");
        PTE_result.hit++;
    }
    
    return PTE[VPN].PPN;
}

int fetchDataToMemory(u32 address) //will return PPN
{
    u32 return_PPN;
    u32 p_add;
    int i;
    
    if (PPN_index<PPN_MAX)
    {
        return_PPN=PPN_index;
        push(&LRU_memory,PPN_index);
        PPN_index++;
    }
    else
    {
        //LRU
        return_PPN=pop(&LRU_memory);
        PTE[PPNtoVPN[return_PPN]].validBit=0;/**if LRU, change one valid bit to zero*/
        for (i=0;i<page_size;i++)
        {
            p_add=(return_PPN<<getPow(page_size))|(i);
            changeCacheValidBit(p_add);
        }
        push(&LRU_memory,return_PPN);
    }
    
    return return_PPN;
}
//void push (int *array,int length,int data)
void push(struct LRU_queue *LRU_queue,int data)
{
    int *queue = LRU_queue->queue;
    int i,j;
    
    for (i=0;i<LRU_queue->length;i++) //if data hit and already exist, delete it
        if (queue[i]==data)
        {
            for (j=i;j<LRU_queue->length;j++)
            {
                if (j<LRU_queue->length-1)
                    queue[j]=queue[j+1];
                else{
                    LRU_queue->length--;
                    break;
                }
            }
            break;
        }
    
    queue[LRU_queue->length]=data; // add at queue's end
    LRU_queue->length++;
}

int pop(struct LRU_queue *LRU_queue)
{
    int *queue = LRU_queue->queue;
    int return_PPN = queue[0]; //replay PPN at queue[0]
    int i;
    for (i=0;i<LRU_queue->length-1;i++)
    {
        queue[i]=queue[i+1];
    }
    LRU_queue->length--;
    
    return return_PPN;
}

int getPow(u32 input)
{
    u32 i;
    if (input==1)
        return 0;
    for (i=1;i<=input/2;i++)
        if (pow(2,i)==input)
            return i;
    
    printf("pow error!");
    exit(1);
    return -1;
}
