//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        reg             finish_r, finish_w;
        reg             IMEM_cen_r, IMEM_cen_w;
        reg [BIT_W-1:0] DMEM_addr_r, DMEM_addr_w;
        reg [BIT_W-1:0] DMEM_wdata_r, DMEM_wdata_w;
        reg             DMEM_cen_r, DMEM_cen_w;
        reg             DMEM_wen_r, DMEM_wen_w;
        reg             DMEM_stall_r, DMEM_stall_w;
        reg             proc_finish_r, proc_finish_w;

        reg             valid_counter;

        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;

        assign  o_IMEM_addr     =   PC;
        assign  o_IMEM_cen      =   IMEM_cen_r;

        assign  o_DMEM_cen      =   DMEM_cen_r;
        assign  o_DMEM_wen      =   DMEM_wen_r;
        assign  o_DMEM_addr     =   DMEM_addr_r;
        assign  o_DMEM_wdata    =   DMEM_wdata_r;


        assign  o_finish        =   finish_r;

        assign  o_proc_finish   =   proc_finish_r;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
        wire                Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite, ALU_branch, Jalr, pc_write, auipc, mul, done;
        wire                MUL_stall, CPU_stall, mul_ready;
        wire    [1:0]       ALUOp;
        wire    [3:0]       ALU_ctrl;
        wire    [BIT_W-1:0] rdata1, rdata2, wdata, imm_gen, i_ALU_2, ALU_output, mul_output; 


        assign  i_ALU_2         =   ALUSrc      ? imm_gen       : rdata2;

        // pc_write: when pc is written to reg; pc_write == 1'b1 for jal, jalr and auipc, otherwise pc_write == 1'b0
        // auipc == 1'b1 for auipc, otherwise auipc == 1'b0

        // write to reg analysis:
        // auipc: write pc+imm_gen to rd
        // jal  : write pc+4 to rd
        // jalr : write pc+4 to rd
        // other: write ALU_output to rd
        assign  wdata           =   MemtoReg    ? i_DMEM_rdata  : (pc_write?(auipc?(PC+imm_gen):(PC+32'd4)):(mul ? mul_output : ALU_output));
        // assign  o_DMEM_addr     =   ALU_output;
        // assign  o_DMEM_wdata    =   rdata2;
        // assign  o_DMEM_wen      =   MemWrite; 
        // assign  o_DMEM_cen      =   MemWrite    | MemRead;

        assign  CPU_stall   =   i_DMEM_stall    ||  MUL_stall;

       



// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Control control0(
        .inst(i_IMEM_data),
        .i_stall(CPU_stall),
        .o_ALUSrc(ALUSrc),
        .o_MemRead(MemRead),
        .o_MemtoReg(MemtoReg),
        .o_ALU_ctrl(ALU_ctrl),
        .o_MemWrite(MemWrite),
        .o_Branch(Branch),
        .o_RegWrite(RegWrite),
        .o_Jalr(Jalr),
        .o_pc_write(pc_write),
        .o_auipc(auipc),
        .o_mul(mul),
        .o_done(done)
    );

  


    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),          
        .rs1    (i_IMEM_data[19:15]),                
        .rs2    (i_IMEM_data[24:20]),                
        .rd     (i_IMEM_data[11:7]),                 
        .wdata  (wdata),             
        .rdata1 (rdata1),           
        .rdata2 (rdata2)
    );

    Imm_Gen imm_gen0(
        .i_inst(i_IMEM_data),
        .o_imm(imm_gen)
    );


    ALU alu0(
        .i_data1(rdata1),
        .i_data2(i_ALU_2),
        .i_ALU_ctrl(ALU_ctrl),
        .o_ALU_output(ALU_output),
        .o_branch(ALU_branch)
    );

    MULDIV_unit mul0(
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_data1(rdata1),
        .i_data2(rdata2),
        .i_valid(mul),
        .o_ready(mul_ready),
        .o_MUL_stall(MUL_stall),
        .o_mul_output(mul_output)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit

    always @(*) begin
        // next_PC =   (Branch && ALU_branch) ? (PC + imm_gen) : (PC + 32'd4);

        // jumping (next_PC) analysis:
        // jal      : jump to pc+imm_gen
        // jalr     : jump to rdata1+imm_gen
        // branch   : jump to pc+imm_gen
        // other    : next_PC = PC+4

        if(IMEM_cen_w == 1'b0 || ((MemRead || MemWrite || mul) && IMEM_cen_r == 1'b1)) begin
            next_PC     =   PC;
        end
        else begin
            if(Branch && ALU_branch) begin
                if(Jalr == 1'b1) begin  // Jalr == 1'b1 when inst is jalr, otherwise Jalr == 1'b0
                    next_PC     =   rdata1  +   imm_gen;
                end
                else begin
                    next_PC     =   PC      +   imm_gen;
                end
            end
            else begin
                next_PC     =   PC  +   32'd4;
            end
        end

        IMEM_cen_w      =   (finish_w | CPU_stall) ? 1'b0 : 1'b1;
        
        finish_w        =   (i_cache_finish)  ?   1'b1    :   1'b0;
        // finish_w        =   (done)  ?   1'b1    :   1'b0;

        DMEM_addr_w     =   ALU_output;
        DMEM_wdata_w    =   rdata2;
        DMEM_wen_w      =   MemWrite; 
        
        DMEM_cen_w      =   (MemWrite || MemRead) && (IMEM_cen_r);

        DMEM_stall_w    =   i_DMEM_stall;

        proc_finish_w   =   done;

        

    end

    // always @(posedge i_clk) begin

    //     // display instruction 
    //     case(i_IMEM_data[6:0]) 
    //         7'b0010111: $display("AUIPC");
    //         7'b1101111: $display("JAL");
    //         7'b1100111: $display("JALR");
    //         7'b0110011: begin
    //             case(i_IMEM_data[14:12])
    //                 3'b000: begin
    //                     if(i_IMEM_data[30] == 1'b1) $display("SUB");
    //                     else if(i_IMEM_data[25] == 1'b1) $display("MUL");
    //                     else $display("ADD");
    //                 end
    //                 3'b111: $display("AND");
    //                 3'b100: $display("XOR");
    //                 default: $display("%b", i_IMEM_data);
    //             endcase
    //         end
    //         7'b0010011: begin
    //             case(i_IMEM_data[14:12])
    //                 3'b000: $display("ADDI");
    //                 3'b001: $display("SLLI");
    //                 3'b010: $display("SLTI");
    //                 3'b101: $display("SRAI");
    //                 default: $display("%b", i_IMEM_data);
    //             endcase 
    //         end
    //         7'b0000011: $display("lw");
    //         7'b0100011: $display("sw");
    //         7'b1100011: begin
    //             case(i_IMEM_data[14:12])
    //                 3'b000: $display("BEQ");
    //                 3'b001: $display("BNE");
    //                 3'b100: $display("BLT");
    //                 3'b101: $display("BGE");
    //                 default: $display("%b", i_IMEM_data);
    //             endcase 
    //         end
    //         7'b1110011: $display("ecall");
    //         default:    $display("%b", i_IMEM_data);
    //     endcase
    // end



    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC              <=  32'h00010000; // Do not modify this value!!!
            IMEM_cen_r      <=  1;
            finish_r        <=  0;

            DMEM_cen_r      <=  0;
            DMEM_wen_r      <=  0;
            DMEM_addr_r     <=  0;
            DMEM_wdata_r    <=  0;

            DMEM_stall_r    <=  0;
            proc_finish_r   <=  0;
        end
        

        else begin
            PC              <=  next_PC;
            IMEM_cen_r      <=  IMEM_cen_w;
            finish_r        <=  finish_w;

            DMEM_cen_r      <=  DMEM_cen_w;
            DMEM_wen_r      <=  DMEM_wen_w;
            DMEM_addr_r     <=  DMEM_addr_w;
            DMEM_wdata_r    <=  DMEM_wdata_w;

            DMEM_stall_r    <=  DMEM_stall_w;
            proc_finish_r   <=  proc_finish_w;
        end
    end
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule


module Control(
    input   [31:0]  inst,
    input           i_stall,
    output          o_ALUSrc,
    output          o_MemtoReg,
    output          o_RegWrite,
    output          o_MemRead,
    output          o_MemWrite,
    output          o_Branch,
    output          o_Jalr,
    output          o_pc_write,
    output          o_auipc,
    output          o_mul,
    output          o_done,
    output  [3:0]   o_ALU_ctrl
);
    reg         ALUSrc;
    reg         MemtoReg;
    reg         RegWrite;
    reg         MemRead;
    reg         MemWrite;
    reg         Branch;
    reg         Jalr;
    reg         pc_write;
    reg         auipc;
    reg         mul;
    reg         done;
    reg  [3:0]  ALU_ctrl;

    assign  o_ALUSrc    =   ALUSrc;
    assign  o_MemtoReg  =   MemtoReg;
    assign  o_RegWrite  =   RegWrite;
    assign  o_MemRead   =   MemRead;
    assign  o_MemWrite  =   MemWrite;
    assign  o_Branch    =   Branch;
    assign  o_ALU_ctrl  =   ALU_ctrl;
    assign  o_Jalr      =   Jalr;
    assign  o_pc_write  =   pc_write;
    assign  o_auipc     =   auipc;
    assign  o_mul       =   mul;
    assign  o_done      =   done;

    // opcode table
    parameter   R_format    =   7'b0110011;
    parameter   I_format    =   7'b0010011;
    parameter   lw          =   7'b0000011;
    parameter   sw          =   7'b0100011;
    parameter   branch      =   7'b1100011;
    parameter   aui         =   7'b0010111;
    parameter   jal         =   7'b1101111;
    parameter   jalr        =   7'b1100111;
    parameter   ecall       =   7'b1110011;
    

    // alu operation table
    parameter   AND     =   4'b0000;
    parameter   XOR     =   4'b0001;
    parameter   ADD     =   4'b0010;
    parameter   SUB     =   4'b0110;
    parameter   SLLI    =   4'b0011;
    parameter   SRAI    =   4'b0100;
    parameter   SLTI    =   4'b0101;
    parameter   BEQ     =   4'b0111;
    parameter   BNE     =   4'b1000;
    parameter   BLT     =   4'b1001;
    parameter   BGE     =   4'b1010;
    parameter   JAL     =   4'b1011;
    parameter   JALR    =   4'b1100;
    parameter   NOTHING =   4'b1111;

    // wire assignment
    wire    [6:0]   opcode;
    wire    [3:0]   funct3;
    assign  opcode  =   inst[6:0];
    assign  funct3  =   inst[14:12];


    always @(*) begin

        if(i_stall == 1'b1) begin
            ALUSrc      =   1'b0;
            MemtoReg    =   1'b0;
            RegWrite    =   1'b0;
            MemRead     =   1'b0;
            MemWrite    =   1'b0;
            Branch      =   1'b0;
            Jalr        =   1'b0;
            pc_write    =   1'b0;
            auipc       =   1'b0;
            mul         =   1'b0;
            done        =   1'b0;
            ALU_ctrl    =   NOTHING;
        end
        else begin
            case(opcode)
                R_format: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b1;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   inst[25] ? 1'b1 : 1'b0;
                    done        =   1'b0;
                    case(funct3)
                        3'b000: ALU_ctrl    =   inst[30]    ?   SUB :   (inst[25] ? NOTHING : ADD);
                        3'b111: ALU_ctrl    =   AND;
                        3'b100: ALU_ctrl    =   XOR;
                        default: ALU_ctrl   =   NOTHING;    // default NOTHING
                    endcase
                    
                end

                I_format: begin
                    ALUSrc      =   1'b1;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b1;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    case(funct3)
                        3'b000: ALU_ctrl    =   ADD;
                        3'b001: ALU_ctrl    =   SLLI;
                        3'b010: ALU_ctrl    =   SLTI;
                        3'b101: ALU_ctrl    =   SRAI;
                        default: ALU_ctrl   =   NOTHING;    // default NOTHING
                    endcase

                end

                lw: begin
                    ALUSrc      =   1'b1;
                    MemtoReg    =   1'b1;
                    RegWrite    =   1'b1;
                    MemRead     =   1'b1;
                    MemWrite    =   1'b0;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    ALU_ctrl    =   ADD;
                end

                sw: begin
                    ALUSrc      =   1'b1;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b0;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b1;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    ALU_ctrl    =   ADD;
                end

                branch: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b0;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b1;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    case(funct3)
                        3'b000:  ALU_ctrl    =   BEQ;
                        3'b001:  ALU_ctrl    =   BNE;
                        3'b100:  ALU_ctrl    =   BLT;
                        3'b101:  ALU_ctrl    =   BGE;
                        default: ALU_ctrl    =   NOTHING;    // default NOTHING
                    endcase
                end

                aui: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b1;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b1;
                    auipc       =   1'b1;
                    mul         =   1'b0;
                    done        =   1'b0;
                    ALU_ctrl    =   NOTHING;
                end

                jal: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b1;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b1;
                    Jalr        =   1'b0;
                    pc_write    =   1'b1;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    ALU_ctrl    =   JAL;
                end

                jalr: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b1;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b1;
                    Jalr        =   1'b1;
                    pc_write    =   1'b1;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    ALU_ctrl    =   JALR;
                end

                ecall: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b0;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b1;
                    ALU_ctrl    =   NOTHING;
                end

                default: begin
                    ALUSrc      =   1'b0;
                    MemtoReg    =   1'b0;
                    RegWrite    =   1'b0;
                    MemRead     =   1'b0;
                    MemWrite    =   1'b0;
                    Branch      =   1'b0;
                    Jalr        =   1'b0;
                    pc_write    =   1'b0;
                    auipc       =   1'b0;
                    mul         =   1'b0;
                    done        =   1'b0;
                    ALU_ctrl    =   NOTHING;
                end
            endcase
        end
    end
endmodule




module ALU # (
    parameter   BIT_W = 32
)(
    input   [BIT_W-1:0]     i_data1,
    input   [BIT_W-1:0]     i_data2,
    input   [3:0]           i_ALU_ctrl,
    output                  o_branch,
    output  [BIT_W-1:0]     o_ALU_output
);
    reg                 branch;
    reg     [BIT_W-1:0] ALU_output;

    assign  o_branch        =   branch;
    assign  o_ALU_output    =   ALU_output;


    parameter   AND     =   4'b0000;
    parameter   XOR     =   4'b0001;
    parameter   ADD     =   4'b0010;
    parameter   SUB     =   4'b0110;
    parameter   SLLI    =   4'b0011;
    parameter   SRAI    =   4'b0100;
    parameter   SLTI    =   4'b0101;
    parameter   BEQ     =   4'b0111;
    parameter   BNE     =   4'b1000;
    parameter   BLT     =   4'b1001;
    parameter   BGE     =   4'b1010;
    parameter   JAL     =   4'b1011;
    parameter   JALR    =   4'b1100;
    parameter   NOTHING =   4'b1111;

    wire signed [BIT_W-1:0] signed_1;
    wire signed [BIT_W-1:0] signed_2;
    wire        [4:0]       shamt;

    assign  signed_1    =   i_data1;
    assign  signed_2    =   i_data2;
    assign  shamt       =   i_data2[4:0];


    always @(*) begin
        case(i_ALU_ctrl)
            AND     : begin
                ALU_output    =   i_data1 & i_data2;
                branch        =   1'b0; 
            end
            XOR     : begin
                ALU_output    =   i_data1 ^ i_data2;
                branch        =   1'b0; 
            end
            ADD     : begin
                ALU_output    =   i_data1 + i_data2;
                branch        =   1'b0; 
            end
            SUB     : begin
                ALU_output    =   i_data1 - i_data2;
                branch        =   1'b0; 
            end
            SLLI    : begin
                ALU_output    =   signed_1 << shamt;
                branch        =   1'b0; 
            end
            SRAI    : begin
                ALU_output    =   signed_1 >>> shamt;
                branch        =   1'b0; 
            end
            SLTI    : begin
                ALU_output    =   (signed_1 < signed_2) ? 32'd1 : 32'd0;
                branch        =   1'b0; 
            end
            BEQ     : begin
                ALU_output    =   32'd0;
                branch        =   (signed_1 == signed_2) ? 1'b1 : 1'b0;
            end
            BNE     : begin
                ALU_output    =   32'd0;
                branch        =   (signed_1 != signed_2) ? 1'b1 : 1'b0;
            end
            BLT     : begin
                ALU_output    =   32'd0;
                branch        =   (signed_1 < signed_2) ? 1'b1 : 1'b0;
            end
            BGE     : begin
                ALU_output    =   32'd0;
                branch        =   (signed_1 > signed_2 || signed_1 == signed_2) ? 1'b1 : 1'b0;
            end
            JAL    : begin
                ALU_output    =   32'd0;
                branch        =   1'b1;
            end
            JALR    : begin
                ALU_output    =   32'd0;
                branch        =   1'b1;
            end
            NOTHING : begin
                ALU_output    =   32'd0;
                branch        =   1'b0; 
            end 
            default : begin
                ALU_output    =   32'd0;
                branch        =   1'b0;
            end
        endcase
    end
endmodule


module Imm_Gen # (
    parameter   BIT_W = 32
)(
    input   [BIT_W-1:0]     i_inst,
    output  [BIT_W-1:0]     o_imm
);
    reg     [BIT_W-1:0] imm;
    wire    [BIT_W-1:0] inst;
    assign  o_imm   =   imm;
    assign  inst    =   i_inst;

    parameter   lw      =   7'b0000011;
    parameter   sw      =   7'b0100011;
    parameter   branch  =   7'b1100011;
    parameter   jal     =   7'b1101111;
    parameter   jalr    =   7'b1100111;
    parameter   auipc   =   7'b0010111;
    parameter   addi    =   7'b0010011;

    always @(*) begin
        case(i_inst[6:0])
            lw      :   imm   =   inst[31] ? {20'hfffff, inst[31:20]} : {20'd0, inst[31:20]};
            sw      :   imm   =   inst[31] ? {20'hfffff, inst[31:25], inst[11:7]} : {20'd0, inst[31:25], inst[11:7]};
            branch  :   imm   =   inst[31] ? {20'hfffff, inst[31], inst[7], inst[30:25], inst[11:8], 1'b0} : {20'd0, inst[31], inst[7], inst[30:25], inst[11:8], 1'b0};
            jal     :   imm   =   inst[31] ? {11'h7ff, inst[31], inst[19:12], inst[20], inst[30:21], 1'b0} : {11'd0, inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};
            jalr    :   imm   =   inst[31] ? {20'hfffff, inst[31:20]} : {20'd0, inst[31:20]};
            auipc   :   imm   =   {inst[31:12], 12'd0};
            addi    :   imm   =   inst[31] ? {20'hfffff, inst[31:20]} : {20'd0, inst[31:20]};
            default :   imm   =   32'd0;
        endcase
    end
endmodule





module MULDIV_unit #(
    parameter   BIT_W = 32
)(
    input                   i_clk,
    input                   i_rst_n,
    input                   i_valid,
    input   [BIT_W-1:0]     i_data1,
    input   [BIT_W-1:0]     i_data2,
    output                  o_ready,
    output                  o_MUL_stall,
    output  [BIT_W-1:0]     o_mul_output
    // TODO: port declaration
    );
    parameter   S_IDLE  =   3'd0;
    parameter   S_MUL   =   3'd1;
    parameter   S_DONE  =   3'd2;

    reg     [8:0]           counter_r, counter_w;
    reg     [2:0]           state_r, state_w;
    reg     [2*BIT_W-1:0]   output_r, output_w;
    reg                     ready_r, ready_w;
    reg                     stall_r, stall_w;

    assign  o_ready         =   ready_r;
    assign  o_mul_output    =   output_r[BIT_W-1:0];
    assign  o_MUL_stall     =   stall_r;

    always @(*) begin

        counter_w   =   counter_r;
        state_w     =   state_r;
        stall_w     =   stall_r;
        ready_w     =   ready_r;
        output_w    =   output_r;

        case(state_r)
        S_IDLE: begin
            if(!i_valid) begin
                state_w     =   state_r;
                output_w    =   0;
                stall_w     =   stall_r;
            end
            else begin
                state_w     =   S_MUL;
                output_w    =   {32'd0, i_data1};
                stall_w     =   1'b1;
            end
        end

        S_MUL: begin
            if(counter_r == 8'd31) begin
                counter_w   =   0;
                state_w     =   S_DONE;
                ready_w     =   1'b1;
                stall_w     =   1'b0; //*
            end
            else begin
                counter_w   =   counter_r   +   8'd1;
                state_w     =   state_r;
                ready_w     =   1'b0;
                stall_w     =   stall_r;
            end

            if(output_r[0] == 1'b1) begin
                output_w    =   (output_r >> 1) + {1'b0, i_data2, 31'd0};
            end
            else begin
                output_w    =   output_r >> 1;
            end
        end

        S_DONE: begin
            ready_w     =   1'b0;
            counter_w   =   0;
            state_w     =   S_IDLE;
            stall_w     =   stall_r;
        end

        default:    state_w =   state_r;

        endcase



    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state_r     <=  S_IDLE;
            counter_r   <=  0;
            output_r    <=  0;
            ready_r     <=  0;
            stall_r     <=  0;
        end
        else begin
            state_r     <=  state_w;
            counter_r   <=  counter_w;
            output_r    <=  output_w;
            ready_r     <=  ready_w;
            stall_r     <=  stall_w;
        end
    end

    // Todo: HW2
endmodule



module Cache#(
        parameter BIT_W     =   32,
        parameter ADDR_W    =   32,
        parameter SIZE      =   32,
        parameter TAG_W     =   26
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            // output [BIT_W-1:0]  o_mem_wdata,
            // input [BIT_W-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available,
            input  [ADDR_W-1: 0] i_offset
    );

    // assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    // ------------------------------------------//
    //          default connection              //
    // assign o_mem_cen = i_proc_cen;              //
    // assign o_mem_wen = i_proc_wen;              //
    // assign o_mem_addr = i_proc_addr;            //
    // assign o_mem_wdata = i_proc_wdata;          //
    // assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    // assign o_proc_stall = i_mem_stall;          //
    // ------------------------------------------//

    // -------------------------------------------------------//
    // Todo: BONUS

    assign o_cache_available = 1;

    // FSM
    parameter   S_IDLE  =   3'd0;
    parameter   S_READ  =   3'd1;
    parameter   S_WRITE =   3'd2;
    parameter   S_ALLO  =   3'd3;
    parameter   S_WB    =   3'd4;
    parameter   S_STORE =   3'd5;
    parameter   S_DONE  =   3'd6;

    // reg
    reg     [2:0]           state_r, state_w;
    reg                     write_r, write_w;
    reg     [BIT_W-1:0]     cache_r [0:SIZE-1];
    reg     [BIT_W-1:0]     cache_w [0:SIZE-1];
    reg     [TAG_W-1:0]     tag_r   [0:SIZE-1];
    reg     [TAG_W-1:0]     tag_w   [0:SIZE-1];
    reg                     valid_r [0:SIZE-1];
    reg                     valid_w [0:SIZE-1];
    reg                     dirty_r [0:SIZE-1];
    reg                     dirty_w [0:SIZE-1];

    reg                     mem_cen_r, mem_cen_w, mem_wen_r, mem_wen_w, proc_stall_r, proc_stall_w;
    reg     [BIT_W-1:0]     mem_addr_r, mem_addr_w, proc_addr_r, proc_addr_w, proc_wdata_w, proc_wdata_r;
    reg     [BIT_W-1:0]     proc_rdata_r, proc_rdata_w;
    reg     [BIT_W-1:0]     addr_real_r, addr_real_w; // real address to memory
    reg     [BIT_W*4-1:0]   mem_wdata_r, mem_wdata_w;
    // reg     [BIT_W-1:0]     mem_wdata_r, mem_wdata_w;
    reg                     write_done_r, write_done_w;
    reg     [7:0]           check_r, check_w;
    reg                     store_r, store_w;
    reg                     store_done_r, store_done_w;
    reg                     cache_finish_r, cache_finish_w;
    reg     [4:0]           set_offset_r, set_offset_w;
    reg     [3:0]           record_r, record_w;

    // wire
    wire    [25:0]          addr_tag;
    wire    [3:0]           addr_index;
    wire    [3:0]           index_real;
    // wire    [1:0]           inblock_index;
    // wire    [4:0]           addr_base_index;
    wire     [3:0]          addr;

    integer i;
    
    // address tag & address index
    assign  addr_tag        =   proc_addr_r[31:6];
    assign  addr_index      =   proc_addr_r[5:2] - {2'd0, i_offset[3:2]};               // 0 ~ 15
    assign  index_real      =   {(proc_addr_r[5:2] - {2'd0, i_offset[3:2]})>>2, 2'd0};  // 0, 4, 8, 12
    // assign  inblock_index   =   proc_addr_r[3:2];
    // assign  addr_base_index =   {proc_addr_r[6:4], 2'd0};

    // output 
    assign  o_mem_cen       =   mem_cen_r;
    assign  o_mem_wen       =   mem_wen_r;
    assign  o_mem_addr      =   mem_addr_r;
    assign  o_mem_wdata     =   mem_wdata_r;
    assign  o_proc_rdata    =   proc_rdata_r;
    assign  o_proc_stall    =   (state_r == S_IDLE && i_proc_cen)? 1'b1 : proc_stall_r;
    assign  o_cache_finish  =   cache_finish_r;

    assign  addr            =   (i_proc_addr[5:2] - {2'd0, i_offset[3:2]});


    always @(*) begin
        // default
        state_w         =   state_r;
        write_w         =   write_r;
        mem_cen_w       =   mem_cen_r;
        mem_wen_w       =   mem_wen_r;
        mem_addr_w      =   mem_addr_r;
        proc_addr_w     =   proc_addr_r;
        proc_wdata_w    =   proc_wdata_r;
        proc_rdata_w    =   proc_rdata_r;
        mem_wdata_w     =   mem_wdata_r;
        proc_stall_w    =   proc_stall_r;
        addr_real_w     =   addr_real_r;
        check_w         =   check_r;
        store_w         =   store_r;
        cache_finish_w  =   cache_finish_r;
        store_done_w    =   store_done_r;
        set_offset_w    =   set_offset_r;
        record_w        =   record_r;

        write_done_w    =   write_done_r;

        for (i=0; i<SIZE; i=i+1) begin
            cache_w[i]  =   cache_r[i];
            tag_w[i]    =   tag_r[i];
            valid_w[i]  =   valid_r[i];
            dirty_w[i]  =   dirty_r[i];
        end
     

        case(state_r)
        S_IDLE: begin
            // proc_addr_w     =   i_proc_addr;

            if(i_proc_cen && i_proc_wen) begin
                // write
                state_w         =   S_WRITE;
                write_w         =   1'b1;
                proc_stall_w    =   1'b1;
                proc_wdata_w    =   i_proc_wdata;
                proc_addr_w     =   i_proc_addr;
                addr_real_w     =   {i_proc_addr[31:6], addr[3:2], i_offset[3:2], 2'd0};
                
            end
            else if(i_proc_cen && !i_proc_wen) begin
                // read
                state_w         =   S_READ;
                write_w         =   1'b0;
                proc_stall_w    =   1'b1;
                proc_addr_w     =   i_proc_addr;
                addr_real_w     =   {i_proc_addr[31:6], addr[3:2], i_offset[3:2], 2'd0};
            end
            else if(i_proc_finish) begin
                // finish --> store cache dirty data into memory
                state_w         =   S_STORE; 
                store_w         =   1'b1;
            end
            else begin
                state_w         =   state_r;
                proc_stall_w    =   proc_stall_r;
                proc_addr_w     =   0;
                proc_rdata_w    =   0;
                addr_real_w     =   0;
                store_w         =   0;
                write_w         =   0;
            end

        end

        S_READ: begin
            if(valid_r[addr_index] == 1'b0) begin  // cache not valid
                state_w         =   S_ALLO;
                mem_cen_w       =   1'b1;
                mem_wen_w       =   1'b0;
                mem_addr_w      =   addr_real_r;
                set_offset_w    =   0;
            end
            else if(tag_r[addr_index] != addr_tag && valid_r[addr_index+16] == 1'b0) begin
                // second set
                state_w         =   S_ALLO;
                mem_cen_w       =   1'b1;
                mem_wen_w       =   1'b0;
                mem_addr_w      =   addr_real_r;
                set_offset_w    =   5'd16;
            end
            else begin  // cache valid
                if(tag_r[addr_index] == addr_tag) begin  // hit
                    state_w         =   S_IDLE;
                    proc_rdata_w    =   cache_r[addr_index];
                    proc_stall_w    =   1'b0;
                end
                else if(tag_r[addr_index+16] == addr_tag) begin
                    state_w         =   S_IDLE;
                    proc_rdata_w    =   cache_r[addr_index+16];
                    proc_stall_w    =   1'b0;
                end
                else begin
                    // read miss --> fetch data from memory (S_ALLO)
                    if(dirty_r[index_real] == 1'b0 && dirty_r[index_real+1] == 1'b0 && dirty_r[index_real+2] == 1'b0 && dirty_r[index_real+3] == 1'b0) begin
                        state_w         =   S_ALLO;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b0;
                        mem_addr_w      =   addr_real_r;
                        set_offset_w    =   0;
                    end
                    else if(dirty_r[index_real+16] == 1'b0 && dirty_r[index_real+17] == 1'b0 && dirty_r[index_real+18] == 1'b0 && dirty_r[index_real+19] == 1'b0) begin
                        state_w         =   S_ALLO;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b0;
                        mem_addr_w      =   addr_real_r;
                        set_offset_w    =   5'd16;
                    end
                    else begin  // miss and the block is dirty --> have to write back first
                        state_w         =   S_WB;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b1;
                        if(record_r[index_real[3:2]] == 0) begin
                            mem_addr_w      =   {tag_r[addr_index], index_real[3:2], i_offset[3:2], 2'b00};
                            mem_wdata_w     =   {cache_r[index_real+3], cache_r[index_real+2], cache_r[index_real+1], cache_r[index_real]};
                            set_offset_w    =   0;
                        end
                        else begin
                            mem_addr_w      =   {tag_r[addr_index+16], index_real[3:2], i_offset[3:2], 2'b00};
                            mem_wdata_w     =   {cache_r[index_real+19], cache_r[index_real+18], cache_r[index_real+17], cache_r[index_real+16]};
                            set_offset_w    =   5'd16;
                        end
                        // (!) always WB the first set 
                    end
                end
            end

        end

        S_WRITE: begin
            // -------------------------------------------------------------------- //
            // ---------------------------- new design ---------------------------- //
            // -------------------------------------------------------------------- //

            if(valid_r[addr_index] == 1'b0) begin  
                // cache block hasn't been initialize (valid == 0)
                state_w         =   S_ALLO;
                mem_cen_w       =   1'b1;
                mem_wen_w       =   1'b0;
                mem_addr_w      =   addr_real_r;
                set_offset_w    =   0;
            end
            else if(tag_r[addr_index] != addr_tag && valid_r[addr_index+16] == 1'b0) begin
                state_w         =   S_ALLO;
                mem_cen_w       =   1'b1;
                mem_wen_w       =   1'b0;
                mem_addr_w      =   addr_real_r;
                set_offset_w    =   5'd16;
            end
            else begin
                if(tag_r[addr_index] == addr_tag) begin  
                    // directly write data into cache
                    state_w             =   S_IDLE;
                    cache_w[addr_index] =   proc_wdata_r;
                    dirty_w[addr_index] =   1'b1;
                    proc_stall_w        =   1'b0;
                end
                else if(tag_r[addr_index+16] == addr_tag) begin
                    state_w                 =   S_IDLE;
                    cache_w[addr_index+16]  =   proc_wdata_r;
                    dirty_w[addr_index+16]  =   1'b1;
                    proc_stall_w            =   1'b0;
                end
                else
                    if(dirty_r[index_real] == 1'b0 && dirty_r[index_real+1] == 1'b0 && dirty_r[index_real+2] == 1'b0 && dirty_r[index_real+3] == 1'b0) begin
                        // 1st set cache is not dirty --> fetch from memory and directly write data into cahce
                        state_w         =   S_ALLO;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b0;
                        mem_addr_w      =   addr_real_r;
                        set_offset_w    =   0;
                    end
                    else if(dirty_r[index_real+16] == 1'b0 && dirty_r[index_real+17] == 1'b0 && dirty_r[index_real+18] == 1'b0 && dirty_r[index_real+19] == 1'b0) begin
                        // 2nd set cache is not dirty --> fetch from memory and directly write data into cahce
                        state_w         =   S_ALLO;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b0;
                        mem_addr_w      =   addr_real_r;
                        set_offset_w    =   5'd16;
                    end
                    else begin 
                        // cache is dirty --> have to write back first
                        state_w         =   S_WB;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b1;
                        if(record_r[index_real[3:2]] == 0) begin
                            mem_addr_w      =   {tag_r[addr_index], index_real[3:2], i_offset[3:2], 2'b00};
                            mem_wdata_w     =   {cache_r[index_real+3], cache_r[index_real+2], cache_r[index_real+1], cache_r[index_real]};
                            set_offset_w    =   0;
                        end
                        else begin
                            mem_addr_w      =   {tag_r[addr_index+16], index_real[3:2], i_offset[3:2], 2'b00};
                            mem_wdata_w     =   {cache_r[index_real+19], cache_r[index_real+18], cache_r[index_real+17], cache_r[index_real+16]};
                            set_offset_w    =   5'd16;
                        end

                    end
                end
            end
        

        S_ALLO: begin  // read from memory
            mem_cen_w       =   1'b0;
            mem_wen_w       =   1'b0;

            if(i_mem_stall) begin
                state_w     =   state_r;
            end 
            else begin
                if(write_r) state_w     =   S_WRITE;
                else        state_w     =   S_READ;

                // store data into cache, update tag, set valid = 1 and dirty = 0
                cache_w[index_real+set_offset_r]     =   i_mem_rdata[0+:BIT_W];
                cache_w[index_real+set_offset_r+1]   =   i_mem_rdata[BIT_W*1+:BIT_W];
                cache_w[index_real+set_offset_r+2]   =   i_mem_rdata[BIT_W*2+:BIT_W];
                cache_w[index_real+set_offset_r+3]   =   i_mem_rdata[BIT_W*3+:BIT_W];

                tag_w[index_real+set_offset_r]       =   addr_tag;
                tag_w[index_real+set_offset_r+1]     =   addr_tag;
                tag_w[index_real+set_offset_r+2]     =   addr_tag;
                tag_w[index_real+set_offset_r+3]     =   addr_tag;
                
                valid_w[index_real+set_offset_r]     =   1'b1;
                valid_w[index_real+set_offset_r+1]   =   1'b1;
                valid_w[index_real+set_offset_r+2]   =   1'b1;
                valid_w[index_real+set_offset_r+3]   =   1'b1;

                dirty_w[index_real+set_offset_r]     =   1'b0;
                dirty_w[index_real+set_offset_r+1]   =   1'b0;
                dirty_w[index_real+set_offset_r+2]   =   1'b0;
                dirty_w[index_real+set_offset_r+3]   =   1'b0;

                record_w[index_real[3:2]]            =   (set_offset_r == 0) ? 1'b1 : 1'b0;

                mem_addr_w          =   0;
                set_offset_w        =   0;
            end

        end

        S_WB: begin  // write back to memory
            mem_cen_w       =   1'b0;
            mem_wen_w       =   1'b0;

            if(i_mem_stall) begin
                state_w     =   state_r;
            end
            else begin
                if(write_r) begin
                    // write inst --> set dirty = 0
                    state_w                 =   S_WRITE;
                    dirty_w[index_real+set_offset_r]     =   1'b0;
                    dirty_w[index_real+set_offset_r+1]   =   1'b0;
                    dirty_w[index_real+set_offset_r+2]   =   1'b0;
                    dirty_w[index_real+set_offset_r+3]   =   1'b0;
                    mem_wdata_w             =   0;
                    mem_addr_w              =   0;
                    record_w[index_real[3:2]]            =   (set_offset_r == 0) ? 1'b1 : 1'b0;

                    // state_w             =   S_IDLE;
                    // proc_stall_w        =   1'b0;
                    // write_done_w        =   1'b1;
                end
                else begin
                    if(store_r == 1'b1) begin
                        state_w         =   S_STORE;
                        mem_wdata_w     =   0;
                        mem_addr_w      =   0;
                        store_done_w    =   1'b1;
                    end
                    else begin
                        // read inst --> start read data
                        state_w         =   S_ALLO;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b0;
                        mem_addr_w      =   addr_real_r;
                    end
                end
            end

        end

        S_STORE: begin
            if(check_r == 8'd8) begin
                state_w         =   S_DONE;
                check_w         =   8'd0;
                cache_finish_w  =   1'b1;
            end
            else begin
                if(store_done_r) begin
                    check_w         =   check_r     +   8'd1;
                    store_done_w    =   0;
                end
                else begin
                    // check_w         =   check_r;
                    // store_done_w    =   store_done_r;
                    if(dirty_r[check_r*4] || dirty_r[check_r*4+1] || dirty_r[check_r*4+2] || dirty_r[check_r*4+3]) begin
                        state_w         =   S_WB;
                        mem_cen_w       =   1'b1;
                        mem_wen_w       =   1'b1;
                        mem_addr_w      =   {tag_r[check_r*4], {check_r[1:0], i_offset[3:2]}, 2'b00};
                        mem_wdata_w     =   {cache_r[check_r*4+3], cache_r[check_r*4+2], cache_r[check_r*4+1], cache_r[check_r*4]};
                    end
                    else begin
                        state_w         =   state_r;
                        check_w         =   check_r     +   8'd1;
                    end

                end

                // $display(check_r*4 + 1);
                // if(dirty_r[check_r*4] || dirty_r[check_r*4+1] || dirty_r[check_r*4+2] || dirty_r[check_r*4+3]) begin
                //     state_w         =   S_WB;
                //     mem_cen_w       =   1'b1;
                //     mem_wen_w       =   1'b1;
                //     mem_addr_w      =   {tag_r[check_r*4], {check_r[1:0], i_offset[3:2]}, 2'b00};
                //     mem_wdata_w     =   {cache_r[check_r*4+3], cache_r[check_r*4+2], cache_r[check_r*4+1], cache_r[check_r*4]};
                // end
                // else begin
                //     state_w         =   state_r;
                //     check_w         =   check_r     +   8'd1;
                // end
            end
        end

        S_DONE: begin
            state_w     =   S_IDLE;
        end

        default: state_w    =   state_r;

        endcase


    end




    always @(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n) begin
            state_r         <=  S_IDLE;
            write_r         <=  0;
            mem_cen_r       <=  0;
            mem_wen_r       <=  0;
            mem_addr_r      <=  0;
            proc_addr_r     <=  0;
            proc_wdata_r    <=  0;
            proc_rdata_r    <=  0;
            mem_wdata_r     <=  0;
            proc_stall_r    <=  0;
            addr_real_r     <=  0;
            check_r         <=  0;
            store_r         <=  0;
            cache_finish_r  <=  0;
            store_done_r    <=  0;
            set_offset_r    <=  0;
            record_r        <=  0;

            write_done_r    <=  0;

            for (i=0; i<SIZE; i=i+1) begin
                cache_r[i]  <=   0;
                tag_r[i]    <=   0;
                valid_r[i]  <=   0;
                dirty_r[i]  <=   0;
            end

        end
        else begin
            state_r         <=   state_w;
            write_r         <=   write_w;
            mem_cen_r       <=   mem_cen_w;
            mem_wen_r       <=   mem_wen_w;
            mem_addr_r      <=   mem_addr_w;
            proc_addr_r     <=   proc_addr_w;
            proc_wdata_r    <=   proc_wdata_w;
            proc_rdata_r    <=   proc_rdata_w;
            mem_wdata_r     <=   mem_wdata_w;
            proc_stall_r    <=   proc_stall_w;
            addr_real_r     <=   addr_real_w;
            check_r         <=   check_w;
            store_r         <=   store_w;
            cache_finish_r  <=   cache_finish_w;
            store_done_r    <=   store_done_w;
            set_offset_r    <=   set_offset_w;
            record_r        <=   record_w;

            write_done_r    <=   write_done_w;

            for (i=0; i<SIZE; i=i+1) begin
                cache_r[i]  <=   cache_w[i];
                tag_r[i]    <=   tag_w[i];
                valid_r[i]  <=   valid_w[i];
                dirty_r[i]  <=   dirty_w[i];
            end

        end

    end

endmodule

