// Copyright 1986-2018 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2018.2 (win64) Build 2258646 Thu Jun 14 20:03:12 MDT 2018
// Date        : Sun Aug 20 04:04:42 2023
// Host        : DESKTOP-A4L7G1R running 64-bit major release  (build 9200)
// Command     : write_verilog -force SPI_netlist.v
// Design      : MASTER_SPI
// Purpose     : This is a Verilog netlist of the current design or from a specific cell of the design. The output is an
//               IEEE 1364-2001 compliant Verilog HDL file that contains netlist information obtained from the input
//               design files.
// Device      : xc7a35ticpg236-1L
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module dbg_hub_CV
   (clk,
    sl_iport0_o,
    sl_oport0_i);
  input clk;
  output [0:36]sl_iport0_o;
  input [0:16]sl_oport0_i;


endmodule

module u_ila_0_CV
   (clk,
    probe0,
    SL_IPORT_I,
    SL_OPORT_O,
    probe1,
    probe2,
    probe3,
    probe4);
  input clk;
  input [0:0]probe0;
  input [0:36]SL_IPORT_I;
  output [0:16]SL_OPORT_O;
  input [0:0]probe1;
  input [0:0]probe2;
  input [0:0]probe3;
  input [0:0]probe4;


endmodule

(* ADDR_SIZE = "8" *) 
(* STRUCTURAL_NETLIST = "yes" *)
module MASTER_SPI
   (clk,
    rst_n,
    SS_n,
    MOSI,
    MISO);
  input clk;
  input rst_n;
  input SS_n;
  input MOSI;
  output MISO;

  wire MISO;
  wire MISO_OBUF;
  wire MOSI;
  wire MOSI_IBUF;
  wire RAM1_n_5;
  wire SPI1_n_1;
  wire SPI1_n_12;
  wire SPI1_n_13;
  wire SPI1_n_14;
  wire SPI1_n_15;
  wire SPI1_n_16;
  wire SPI1_n_17;
  wire SS_n;
  wire SS_n_IBUF;
  wire clk;
  wire clk_IBUF;
  wire clk_IBUF_BUFG;
  wire mem;
  wire rst_n;
  wire rst_n_IBUF;
  wire [7:0]rx_data;
  wire rx_valid;
  wire [0:36]sl_iport0_o_0;
  wire [0:16]sl_oport0_i_0;
  wire [6:0]tx_data;
  wire tx_valid;

  OBUF MISO_OBUF_inst
       (.I(MISO_OBUF),
        .O(MISO));
  IBUF MOSI_IBUF_inst
       (.I(MOSI),
        .O(MOSI_IBUF));
  RAM RAM1
       (.CLK(clk_IBUF_BUFG),
        .DOBDO({tx_data[6],tx_data[4],tx_data[2],tx_data[0]}),
        .E(SPI1_n_12),
        .MISO_reg(RAM1_n_5),
        .Q(rx_data),
        .WEA(mem),
        .\bit_cntr_rd_reg[2] ({SPI1_n_14,SPI1_n_15}),
        .rst_n(SPI1_n_1),
        .\rx_data_reg[8] (SPI1_n_13),
        .\rx_data_reg[9] (SPI1_n_17),
        .\rx_data_reg[9]_0 (SPI1_n_16),
        .rx_valid(rx_valid),
        .tx_valid(tx_valid));
  SPI_SLAVE SPI1
       (.CLK(clk_IBUF_BUFG),
        .DOBDO({tx_data[6],tx_data[4],tx_data[2],tx_data[0]}),
        .E(SPI1_n_12),
        .MISO_OBUF(MISO_OBUF),
        .MOSI_IBUF(MOSI_IBUF),
        .Q(rx_data),
        .SS_n_IBUF(SS_n_IBUF),
        .WEA(mem),
        .\bit_cntr_rd_reg[2]_0 ({SPI1_n_14,SPI1_n_15}),
        .mem_reg(SPI1_n_17),
        .mem_reg_0(RAM1_n_5),
        .\rd_addr_reg[7] (SPI1_n_13),
        .rst_n_IBUF(rst_n_IBUF),
        .rx_valid(rx_valid),
        .rx_valid_reg_0(SPI1_n_1),
        .tx_valid(tx_valid),
        .tx_valid_reg(SPI1_n_16));
  IBUF SS_n_IBUF_inst
       (.I(SS_n),
        .O(SS_n_IBUF));
  BUFG clk_IBUF_BUFG_inst
       (.I(clk_IBUF),
        .O(clk_IBUF_BUFG));
  IBUF clk_IBUF_inst
       (.I(clk),
        .O(clk_IBUF));
  (* CORE_GENERATION_INFO = "dbg_hub,labtools_xsdbm_v3_00_a,{C_BSCAN_MODE=false,C_BSCAN_MODE_WITH_CORE=false,C_CLK_INPUT_FREQ_HZ=300000000,C_ENABLE_CLK_DIVIDER=false,C_EN_BSCANID_VEC=false,C_NUM_BSCAN_MASTER_PORTS=0,C_TWO_PRIM_MODE=false,C_USER_SCAN_CHAIN=1,C_USE_EXT_BSCAN=false,C_XSDB_NUM_SLAVES=1,component_name=dbg_hub_CV}" *) 
  (* DEBUG_PORT_clk = "" *) 
  (* IS_DEBUG_CORE *) 
  dbg_hub_CV dbg_hub
       (.clk(clk_IBUF_BUFG),
        .sl_iport0_o(sl_iport0_o_0),
        .sl_oport0_i(sl_oport0_i_0));
  IBUF rst_n_IBUF_inst
       (.I(rst_n),
        .O(rst_n_IBUF));
  (* CORE_GENERATION_INFO = "u_ila_0,labtools_ila_v6_00_a,{ALL_PROBE_SAME_MU=true,ALL_PROBE_SAME_MU_CNT=1,C_ADV_TRIGGER=false,C_DATA_DEPTH=1024,C_EN_STRG_QUAL=false,C_INPUT_PIPE_STAGES=0,C_NUM_OF_PROBES=5,C_PROBE0_TYPE=2,C_PROBE0_WIDTH=1,C_PROBE1_TYPE=1,C_PROBE1_WIDTH=1,C_PROBE2_TYPE=1,C_PROBE2_WIDTH=1,C_PROBE3_TYPE=0,C_PROBE3_WIDTH=1,C_PROBE4_TYPE=0,C_PROBE4_WIDTH=1,C_TRIGIN_EN=0,C_TRIGOUT_EN=0,component_name=u_ila_0_CV}" *) 
  (* DEBUG_PORT_clk = "n:clk_IBUF_BUFG" *) 
  (* DEBUG_PORT_probe0 = "n:clk_IBUF" *) 
  (* DEBUG_PORT_probe1 = "n:MISO_OBUF" *) 
  (* DEBUG_PORT_probe2 = "n:MOSI_IBUF" *) 
  (* DEBUG_PORT_probe3 = "n:rst_n_IBUF" *) 
  (* DEBUG_PORT_probe4 = "n:SS_n_IBUF" *) 
  (* IS_DEBUG_CORE *) 
  u_ila_0_CV u_ila_0
       (.SL_IPORT_I(sl_iport0_o_0),
        .SL_OPORT_O(sl_oport0_i_0),
        .clk(clk_IBUF_BUFG),
        .probe0(clk_IBUF),
        .probe1(MISO_OBUF),
        .probe2(MOSI_IBUF),
        .probe3(rst_n_IBUF),
        .probe4(SS_n_IBUF));
endmodule

module RAM
   (DOBDO,
    tx_valid,
    MISO_reg,
    CLK,
    rx_valid,
    \rx_data_reg[9] ,
    rst_n,
    Q,
    WEA,
    \rx_data_reg[9]_0 ,
    \bit_cntr_rd_reg[2] ,
    E,
    \rx_data_reg[8] );
  output [3:0]DOBDO;
  output tx_valid;
  output MISO_reg;
  input CLK;
  input rx_valid;
  input \rx_data_reg[9] ;
  input rst_n;
  input [7:0]Q;
  input [0:0]WEA;
  input \rx_data_reg[9]_0 ;
  input [1:0]\bit_cntr_rd_reg[2] ;
  input [0:0]E;
  input [0:0]\rx_data_reg[8] ;

  wire \<const0> ;
  wire \<const1> ;
  wire CLK;
  wire [3:0]DOBDO;
  wire [0:0]E;
  wire MISO_reg;
  wire [7:0]Q;
  wire [0:0]WEA;
  wire [1:0]\bit_cntr_rd_reg[2] ;
  wire [7:0]rd_addr;
  wire rst_n;
  wire [0:0]\rx_data_reg[8] ;
  wire \rx_data_reg[9] ;
  wire \rx_data_reg[9]_0 ;
  wire rx_valid;
  wire [7:1]tx_data;
  wire tx_valid;
  wire [7:0]wr_addr;

  GND GND
       (.G(\<const0> ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    MISO_i_4
       (.I0(tx_data[1]),
        .I1(tx_data[3]),
        .I2(\bit_cntr_rd_reg[2] [1]),
        .I3(tx_data[5]),
        .I4(\bit_cntr_rd_reg[2] [0]),
        .I5(tx_data[7]),
        .O(MISO_reg));
  VCC VCC
       (.P(\<const1> ));
  (* \MEM.PORTA.DATA_BIT_LAYOUT  = "p0_d8" *) 
  (* \MEM.PORTB.DATA_BIT_LAYOUT  = "p0_d8" *) 
  (* METHODOLOGY_DRC_VIOS = "{SYNTH-6 {cell *THIS*}}" *) 
  (* RTL_RAM_BITS = "2048" *) 
  (* RTL_RAM_NAME = "mem" *) 
  (* bram_addr_begin = "0" *) 
  (* bram_addr_end = "1023" *) 
  (* bram_slice_begin = "0" *) 
  (* bram_slice_end = "7" *) 
  RAMB18E1 #(
    .DOA_REG(0),
    .DOB_REG(0),
    .INITP_00(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_01(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_02(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_03(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_04(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_05(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_06(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INITP_07(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_00(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_01(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_02(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_03(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_04(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_05(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_06(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_07(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_08(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_09(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_0A(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_0B(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_0C(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_0D(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_0E(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_0F(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_10(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_11(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_12(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_13(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_14(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_15(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_16(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_17(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_18(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_19(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_1A(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_1B(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_1C(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_1D(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_1E(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_1F(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_20(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_21(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_22(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_23(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_24(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_25(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_26(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_27(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_28(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_29(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_2A(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_2B(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_2C(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_2D(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_2E(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_2F(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_30(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_31(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_32(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_33(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_34(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_35(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_36(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_37(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_38(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_39(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_3A(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_3B(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_3C(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_3D(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_3E(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_3F(256'h0000000000000000000000000000000000000000000000000000000000000000),
    .INIT_A(18'h00000),
    .INIT_B(18'h00000),
    .INIT_FILE("NONE"),
    .RAM_MODE("TDP"),
    .RDADDR_COLLISION_HWCONFIG("DELAYED_WRITE"),
    .READ_WIDTH_A(18),
    .READ_WIDTH_B(18),
    .RSTREG_PRIORITY_A("RSTREG"),
    .RSTREG_PRIORITY_B("RSTREG"),
    .SIM_COLLISION_CHECK("ALL"),
    .SIM_DEVICE("7SERIES"),
    .SRVAL_A(18'h00000),
    .SRVAL_B(18'h00000),
    .WRITE_MODE_A("READ_FIRST"),
    .WRITE_MODE_B("WRITE_FIRST"),
    .WRITE_WIDTH_A(18),
    .WRITE_WIDTH_B(18)) 
    mem_reg
       (.ADDRARDADDR({\<const1> ,\<const1> ,wr_addr,\<const1> ,\<const1> ,\<const1> ,\<const1> }),
        .ADDRBWRADDR({\<const1> ,\<const1> ,rd_addr,\<const1> ,\<const1> ,\<const1> ,\<const1> }),
        .CLKARDCLK(CLK),
        .CLKBWRCLK(CLK),
        .DIADI({\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,Q}),
        .DIBDI({\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const0> ,\<const1> ,\<const1> ,\<const1> ,\<const1> ,\<const1> ,\<const1> ,\<const1> ,\<const1> }),
        .DIPADIP({\<const0> ,\<const0> }),
        .DIPBDIP({\<const0> ,\<const0> }),
        .DOBDO({tx_data[7],DOBDO[3],tx_data[5],DOBDO[2],tx_data[3],DOBDO[1],tx_data[1],DOBDO[0]}),
        .ENARDEN(rx_valid),
        .ENBWREN(\rx_data_reg[9] ),
        .REGCEAREGCE(\<const0> ),
        .REGCEB(\<const0> ),
        .RSTRAMARSTRAM(\<const0> ),
        .RSTRAMB(rst_n),
        .RSTREGARSTREG(\<const0> ),
        .RSTREGB(\<const0> ),
        .WEA({WEA,WEA}),
        .WEBWE({\<const0> ,\<const0> ,\<const0> ,\<const0> }));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[0] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[0]),
        .Q(rd_addr[0]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[1] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[1]),
        .Q(rd_addr[1]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[2] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[2]),
        .Q(rd_addr[2]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[3] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[3]),
        .Q(rd_addr[3]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[4] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[4]),
        .Q(rd_addr[4]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[5] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[5]),
        .Q(rd_addr[5]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[6] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[6]),
        .Q(rd_addr[6]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \rd_addr_reg[7] 
       (.C(CLK),
        .CE(\rx_data_reg[8] ),
        .D(Q[7]),
        .Q(rd_addr[7]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    tx_valid_reg
       (.C(CLK),
        .CE(\<const1> ),
        .D(\rx_data_reg[9]_0 ),
        .Q(tx_valid),
        .R(\<const0> ));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[0] 
       (.C(CLK),
        .CE(E),
        .D(Q[0]),
        .Q(wr_addr[0]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[1] 
       (.C(CLK),
        .CE(E),
        .D(Q[1]),
        .Q(wr_addr[1]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[2] 
       (.C(CLK),
        .CE(E),
        .D(Q[2]),
        .Q(wr_addr[2]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[3] 
       (.C(CLK),
        .CE(E),
        .D(Q[3]),
        .Q(wr_addr[3]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[4] 
       (.C(CLK),
        .CE(E),
        .D(Q[4]),
        .Q(wr_addr[4]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[5] 
       (.C(CLK),
        .CE(E),
        .D(Q[5]),
        .Q(wr_addr[5]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[6] 
       (.C(CLK),
        .CE(E),
        .D(Q[6]),
        .Q(wr_addr[6]),
        .R(rst_n));
  FDRE #(
    .INIT(1'b0)) 
    \wr_addr_reg[7] 
       (.C(CLK),
        .CE(E),
        .D(Q[7]),
        .Q(wr_addr[7]),
        .R(rst_n));
endmodule

module SPI_SLAVE
   (MISO_OBUF,
    rx_valid_reg_0,
    rx_valid,
    WEA,
    Q,
    E,
    \rd_addr_reg[7] ,
    \bit_cntr_rd_reg[2]_0 ,
    tx_valid_reg,
    mem_reg,
    CLK,
    rst_n_IBUF,
    MOSI_IBUF,
    tx_valid,
    mem_reg_0,
    DOBDO,
    SS_n_IBUF);
  output MISO_OBUF;
  output rx_valid_reg_0;
  output rx_valid;
  output [0:0]WEA;
  output [7:0]Q;
  output [0:0]E;
  output [0:0]\rd_addr_reg[7] ;
  output [1:0]\bit_cntr_rd_reg[2]_0 ;
  output tx_valid_reg;
  output mem_reg;
  input CLK;
  input rst_n_IBUF;
  input MOSI_IBUF;
  input tx_valid;
  input mem_reg_0;
  input [3:0]DOBDO;
  input SS_n_IBUF;

  wire \<const1> ;
  wire CLK;
  wire [3:0]DOBDO;
  wire [0:0]E;
  wire MISO_OBUF;
  wire MISO_i_1_n_0;
  wire MISO_i_2_n_0;
  wire MISO_i_3_n_0;
  wire MISO_i_5_n_0;
  wire MISO_i_6_n_0;
  wire MOSI_IBUF;
  wire [7:0]Q;
  wire SS_n_IBUF;
  wire [0:0]WEA;
  wire [4:0]bit_cntr_rd;
  wire \bit_cntr_rd[4]_i_1_n_0 ;
  wire \bit_cntr_rd[4]_i_3_n_0 ;
  wire \bit_cntr_rd[4]_i_4_n_0 ;
  wire \bit_cntr_rd[4]_i_5_n_0 ;
  wire [1:0]\bit_cntr_rd_reg[2]_0 ;
  wire \bit_cntr_rd_reg_n_0_[0] ;
  wire \bit_cntr_rd_reg_n_0_[3] ;
  wire \bit_cntr_rd_reg_n_0_[4] ;
  wire [4:0]bit_cntr_wr;
  wire \bit_cntr_wr[3]_i_2_n_0 ;
  wire \bit_cntr_wr[4]_i_1_n_0 ;
  wire \bit_cntr_wr_reg_n_0_[0] ;
  wire \bit_cntr_wr_reg_n_0_[1] ;
  wire \bit_cntr_wr_reg_n_0_[2] ;
  wire \bit_cntr_wr_reg_n_0_[3] ;
  wire \bit_cntr_wr_reg_n_0_[4] ;
  (* RTL_KEEP = "yes" *) wire [2:0]cs;
  wire data_addr_i_1_n_0;
  wire data_addr_reg_n_0;
  wire mem_reg;
  wire mem_reg_0;
  wire [2:0]ns;
  wire [0:0]\rd_addr_reg[7] ;
  wire rst_n_IBUF;
  wire [9:8]rx_data;
  wire [9:0]rx_data__0;
  wire rx_valid;
  wire rx_valid_i_1_n_0;
  wire rx_valid_i_2_n_0;
  wire rx_valid_reg_0;
  wire tx_valid;
  wire tx_valid_reg;

  LUT6 #(
    .INIT(64'h0F0D0E0D0F0D0F0D)) 
    \FSM_gray_cs[0]_i_1 
       (.I0(cs[1]),
        .I1(cs[2]),
        .I2(SS_n_IBUF),
        .I3(cs[0]),
        .I4(data_addr_reg_n_0),
        .I5(MOSI_IBUF),
        .O(ns[0]));
  LUT4 #(
    .INIT(16'h0F0E)) 
    \FSM_gray_cs[1]_i_1 
       (.I0(cs[0]),
        .I1(cs[2]),
        .I2(SS_n_IBUF),
        .I3(cs[1]),
        .O(ns[1]));
  LUT5 #(
    .INIT(32'h00FF0002)) 
    \FSM_gray_cs[2]_i_1 
       (.I0(cs[0]),
        .I1(MOSI_IBUF),
        .I2(cs[1]),
        .I3(SS_n_IBUF),
        .I4(cs[2]),
        .O(ns[2]));
  (* FSM_ENCODED_STATES = "CHK_CMD:001,WRITE:111,READ_ADD:010,READ_DATA:011,IDLE:000" *) 
  (* KEEP = "yes" *) 
  FDCE #(
    .INIT(1'b0)) 
    \FSM_gray_cs_reg[0] 
       (.C(CLK),
        .CE(\<const1> ),
        .CLR(rx_valid_reg_0),
        .D(ns[0]),
        .Q(cs[0]));
  (* FSM_ENCODED_STATES = "CHK_CMD:001,WRITE:111,READ_ADD:010,READ_DATA:011,IDLE:000" *) 
  (* KEEP = "yes" *) 
  FDCE #(
    .INIT(1'b0)) 
    \FSM_gray_cs_reg[1] 
       (.C(CLK),
        .CE(\<const1> ),
        .CLR(rx_valid_reg_0),
        .D(ns[1]),
        .Q(cs[1]));
  (* FSM_ENCODED_STATES = "CHK_CMD:001,WRITE:111,READ_ADD:010,READ_DATA:011,IDLE:000" *) 
  (* KEEP = "yes" *) 
  FDCE #(
    .INIT(1'b0)) 
    \FSM_gray_cs_reg[2] 
       (.C(CLK),
        .CE(\<const1> ),
        .CLR(rx_valid_reg_0),
        .D(ns[2]),
        .Q(cs[2]));
  LUT6 #(
    .INIT(64'hFFFF0000EFEE0000)) 
    MISO_i_1
       (.I0(MISO_i_2_n_0),
        .I1(MISO_i_3_n_0),
        .I2(\bit_cntr_rd_reg_n_0_[0] ),
        .I3(mem_reg_0),
        .I4(MISO_i_5_n_0),
        .I5(MISO_i_6_n_0),
        .O(MISO_i_1_n_0));
  LUT5 #(
    .INIT(32'h44400040)) 
    MISO_i_2
       (.I0(\bit_cntr_rd_reg[2]_0 [0]),
        .I1(\bit_cntr_rd_reg_n_0_[0] ),
        .I2(DOBDO[3]),
        .I3(\bit_cntr_rd_reg[2]_0 [1]),
        .I4(DOBDO[1]),
        .O(MISO_i_2_n_0));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT4 #(
    .INIT(16'h4000)) 
    MISO_i_3
       (.I0(\bit_cntr_rd_reg[2]_0 [1]),
        .I1(DOBDO[2]),
        .I2(\bit_cntr_rd_reg[2]_0 [0]),
        .I3(\bit_cntr_rd_reg_n_0_[0] ),
        .O(MISO_i_3_n_0));
  LUT5 #(
    .INIT(32'h00001000)) 
    MISO_i_5
       (.I0(\bit_cntr_rd_reg_n_0_[4] ),
        .I1(\bit_cntr_rd_reg_n_0_[3] ),
        .I2(tx_valid),
        .I3(cs[1]),
        .I4(cs[2]),
        .O(MISO_i_5_n_0));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT4 #(
    .INIT(16'h8000)) 
    MISO_i_6
       (.I0(DOBDO[0]),
        .I1(\bit_cntr_rd_reg[2]_0 [1]),
        .I2(\bit_cntr_rd_reg_n_0_[0] ),
        .I3(\bit_cntr_rd_reg[2]_0 [0]),
        .O(MISO_i_6_n_0));
  FDCE #(
    .INIT(1'b0)) 
    MISO_reg
       (.C(CLK),
        .CE(\bit_cntr_rd[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(MISO_i_1_n_0),
        .Q(MISO_OBUF));
  VCC VCC
       (.P(\<const1> ));
  LUT4 #(
    .INIT(16'h0008)) 
    \bit_cntr_rd[0]_i_1 
       (.I0(tx_valid),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(\bit_cntr_rd_reg_n_0_[0] ),
        .O(bit_cntr_rd[0]));
  LUT5 #(
    .INIT(32'h00404000)) 
    \bit_cntr_rd[1]_i_1 
       (.I0(cs[2]),
        .I1(cs[1]),
        .I2(tx_valid),
        .I3(\bit_cntr_rd_reg_n_0_[0] ),
        .I4(\bit_cntr_rd_reg[2]_0 [0]),
        .O(bit_cntr_rd[1]));
  LUT6 #(
    .INIT(64'h0040404040000000)) 
    \bit_cntr_rd[2]_i_1 
       (.I0(cs[2]),
        .I1(cs[1]),
        .I2(tx_valid),
        .I3(\bit_cntr_rd_reg[2]_0 [0]),
        .I4(\bit_cntr_rd_reg_n_0_[0] ),
        .I5(\bit_cntr_rd_reg[2]_0 [1]),
        .O(bit_cntr_rd[2]));
  LUT5 #(
    .INIT(32'h2AAA8000)) 
    \bit_cntr_rd[3]_i_1 
       (.I0(\bit_cntr_rd[4]_i_5_n_0 ),
        .I1(\bit_cntr_rd_reg[2]_0 [1]),
        .I2(\bit_cntr_rd_reg_n_0_[0] ),
        .I3(\bit_cntr_rd_reg[2]_0 [0]),
        .I4(\bit_cntr_rd_reg_n_0_[3] ),
        .O(bit_cntr_rd[3]));
  LUT6 #(
    .INIT(64'hFF00FF00FFFFFFA8)) 
    \bit_cntr_rd[4]_i_1 
       (.I0(\bit_cntr_wr_reg_n_0_[3] ),
        .I1(\bit_cntr_wr_reg_n_0_[1] ),
        .I2(\bit_cntr_wr_reg_n_0_[2] ),
        .I3(\bit_cntr_rd[4]_i_3_n_0 ),
        .I4(\bit_cntr_wr_reg_n_0_[4] ),
        .I5(\bit_cntr_rd[4]_i_4_n_0 ),
        .O(\bit_cntr_rd[4]_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h7FFF000080000000)) 
    \bit_cntr_rd[4]_i_2 
       (.I0(\bit_cntr_rd_reg[2]_0 [1]),
        .I1(\bit_cntr_rd_reg_n_0_[0] ),
        .I2(\bit_cntr_rd_reg[2]_0 [0]),
        .I3(\bit_cntr_rd_reg_n_0_[3] ),
        .I4(\bit_cntr_rd[4]_i_5_n_0 ),
        .I5(\bit_cntr_rd_reg_n_0_[4] ),
        .O(bit_cntr_rd[4]));
  LUT3 #(
    .INIT(8'h4F)) 
    \bit_cntr_rd[4]_i_3 
       (.I0(cs[0]),
        .I1(cs[2]),
        .I2(cs[1]),
        .O(\bit_cntr_rd[4]_i_3_n_0 ));
  LUT2 #(
    .INIT(4'hB)) 
    \bit_cntr_rd[4]_i_4 
       (.I0(cs[2]),
        .I1(cs[0]),
        .O(\bit_cntr_rd[4]_i_4_n_0 ));
  LUT3 #(
    .INIT(8'h40)) 
    \bit_cntr_rd[4]_i_5 
       (.I0(cs[2]),
        .I1(cs[1]),
        .I2(tx_valid),
        .O(\bit_cntr_rd[4]_i_5_n_0 ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_rd_reg[0] 
       (.C(CLK),
        .CE(\bit_cntr_rd[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_rd[0]),
        .Q(\bit_cntr_rd_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_rd_reg[1] 
       (.C(CLK),
        .CE(\bit_cntr_rd[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_rd[1]),
        .Q(\bit_cntr_rd_reg[2]_0 [0]));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_rd_reg[2] 
       (.C(CLK),
        .CE(\bit_cntr_rd[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_rd[2]),
        .Q(\bit_cntr_rd_reg[2]_0 [1]));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_rd_reg[3] 
       (.C(CLK),
        .CE(\bit_cntr_rd[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_rd[3]),
        .Q(\bit_cntr_rd_reg_n_0_[3] ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_rd_reg[4] 
       (.C(CLK),
        .CE(\bit_cntr_rd[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_rd[4]),
        .Q(\bit_cntr_rd_reg_n_0_[4] ));
  LUT4 #(
    .INIT(16'h00A2)) 
    \bit_cntr_wr[0]_i_1 
       (.I0(cs[1]),
        .I1(cs[2]),
        .I2(cs[0]),
        .I3(\bit_cntr_wr_reg_n_0_[0] ),
        .O(bit_cntr_wr[0]));
  LUT5 #(
    .INIT(32'h0033F100)) 
    \bit_cntr_wr[1]_i_1 
       (.I0(\bit_cntr_wr_reg_n_0_[3] ),
        .I1(\bit_cntr_rd[4]_i_3_n_0 ),
        .I2(\bit_cntr_wr[3]_i_2_n_0 ),
        .I3(\bit_cntr_wr_reg_n_0_[0] ),
        .I4(\bit_cntr_wr_reg_n_0_[1] ),
        .O(bit_cntr_wr[1]));
  LUT6 #(
    .INIT(64'h00B0B0B0B0000000)) 
    \bit_cntr_wr[2]_i_1 
       (.I0(cs[0]),
        .I1(cs[2]),
        .I2(cs[1]),
        .I3(\bit_cntr_wr_reg_n_0_[1] ),
        .I4(\bit_cntr_wr_reg_n_0_[0] ),
        .I5(\bit_cntr_wr_reg_n_0_[2] ),
        .O(bit_cntr_wr[2]));
  LUT6 #(
    .INIT(64'h07070808FF050000)) 
    \bit_cntr_wr[3]_i_1 
       (.I0(\bit_cntr_wr_reg_n_0_[0] ),
        .I1(\bit_cntr_wr_reg_n_0_[2] ),
        .I2(\bit_cntr_rd[4]_i_3_n_0 ),
        .I3(\bit_cntr_wr[3]_i_2_n_0 ),
        .I4(\bit_cntr_wr_reg_n_0_[3] ),
        .I5(\bit_cntr_wr_reg_n_0_[1] ),
        .O(bit_cntr_wr[3]));
  LUT5 #(
    .INIT(32'hE0F000E0)) 
    \bit_cntr_wr[3]_i_2 
       (.I0(\bit_cntr_wr_reg_n_0_[4] ),
        .I1(\bit_cntr_wr_reg_n_0_[2] ),
        .I2(cs[1]),
        .I3(cs[2]),
        .I4(cs[0]),
        .O(\bit_cntr_wr[3]_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hBBBBBFBFBBBBBFFF)) 
    \bit_cntr_wr[4]_i_1 
       (.I0(\bit_cntr_rd[4]_i_4_n_0 ),
        .I1(cs[1]),
        .I2(\bit_cntr_wr_reg_n_0_[3] ),
        .I3(\bit_cntr_wr_reg_n_0_[1] ),
        .I4(\bit_cntr_wr_reg_n_0_[4] ),
        .I5(\bit_cntr_wr_reg_n_0_[2] ),
        .O(\bit_cntr_wr[4]_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h00007FFF00008000)) 
    \bit_cntr_wr[4]_i_2 
       (.I0(\bit_cntr_wr_reg_n_0_[3] ),
        .I1(\bit_cntr_wr_reg_n_0_[2] ),
        .I2(\bit_cntr_wr_reg_n_0_[1] ),
        .I3(\bit_cntr_wr_reg_n_0_[0] ),
        .I4(\bit_cntr_rd[4]_i_3_n_0 ),
        .I5(\bit_cntr_wr_reg_n_0_[4] ),
        .O(bit_cntr_wr[4]));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_wr_reg[0] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_wr[0]),
        .Q(\bit_cntr_wr_reg_n_0_[0] ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_wr_reg[1] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_wr[1]),
        .Q(\bit_cntr_wr_reg_n_0_[1] ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_wr_reg[2] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_wr[2]),
        .Q(\bit_cntr_wr_reg_n_0_[2] ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_wr_reg[3] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_wr[3]),
        .Q(\bit_cntr_wr_reg_n_0_[3] ));
  FDCE #(
    .INIT(1'b0)) 
    \bit_cntr_wr_reg[4] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(bit_cntr_wr[4]),
        .Q(\bit_cntr_wr_reg_n_0_[4] ));
  LUT5 #(
    .INIT(32'hD3030200)) 
    data_addr_i_1
       (.I0(SS_n_IBUF),
        .I1(cs[2]),
        .I2(cs[0]),
        .I3(cs[1]),
        .I4(data_addr_reg_n_0),
        .O(data_addr_i_1_n_0));
  FDCE #(
    .INIT(1'b0)) 
    data_addr_reg
       (.C(CLK),
        .CE(\<const1> ),
        .CLR(rx_valid_reg_0),
        .D(data_addr_i_1_n_0),
        .Q(data_addr_reg_n_0));
  LUT3 #(
    .INIT(8'h8F)) 
    mem_reg_i_1
       (.I0(rx_data[9]),
        .I1(rx_data[8]),
        .I2(rst_n_IBUF),
        .O(mem_reg));
  LUT1 #(
    .INIT(2'h1)) 
    mem_reg_i_2
       (.I0(rst_n_IBUF),
        .O(rx_valid_reg_0));
  LUT3 #(
    .INIT(8'h40)) 
    mem_reg_i_3
       (.I0(rx_data[9]),
        .I1(rx_data[8]),
        .I2(rst_n_IBUF),
        .O(WEA));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT3 #(
    .INIT(8'h40)) 
    \rd_addr[7]_i_1 
       (.I0(rx_data[8]),
        .I1(rx_data[9]),
        .I2(rx_valid),
        .O(\rd_addr_reg[7] ));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[0]_i_1 
       (.I0(MOSI_IBUF),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[0]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[1]_i_1 
       (.I0(Q[0]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[1]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[2]_i_1 
       (.I0(Q[1]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[2]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[3]_i_1 
       (.I0(Q[2]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[3]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[4]_i_1 
       (.I0(Q[3]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[4]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[5]_i_1 
       (.I0(Q[4]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[5]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[6]_i_1 
       (.I0(Q[5]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[6]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[7]_i_1 
       (.I0(Q[6]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[7]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[8]_i_1 
       (.I0(Q[7]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[8]));
  LUT4 #(
    .INIT(16'h8808)) 
    \rx_data[9]_i_1 
       (.I0(rx_data[8]),
        .I1(cs[1]),
        .I2(cs[2]),
        .I3(cs[0]),
        .O(rx_data__0[9]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[0] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[0]),
        .Q(Q[0]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[1] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[1]),
        .Q(Q[1]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[2] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[2]),
        .Q(Q[2]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[3] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[3]),
        .Q(Q[3]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[4] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[4]),
        .Q(Q[4]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[5] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[5]),
        .Q(Q[5]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[6] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[6]),
        .Q(Q[6]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[7] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[7]),
        .Q(Q[7]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[8] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[8]),
        .Q(rx_data[8]));
  FDCE #(
    .INIT(1'b0)) 
    \rx_data_reg[9] 
       (.C(CLK),
        .CE(\bit_cntr_wr[4]_i_1_n_0 ),
        .CLR(rx_valid_reg_0),
        .D(rx_data__0[9]),
        .Q(rx_data[9]));
  LUT5 #(
    .INIT(32'h8E008200)) 
    rx_valid_i_1
       (.I0(rx_valid_i_2_n_0),
        .I1(cs[0]),
        .I2(cs[2]),
        .I3(cs[1]),
        .I4(rx_valid),
        .O(rx_valid_i_1_n_0));
  LUT5 #(
    .INIT(32'h00000008)) 
    rx_valid_i_2
       (.I0(\bit_cntr_wr_reg_n_0_[0] ),
        .I1(\bit_cntr_wr_reg_n_0_[3] ),
        .I2(\bit_cntr_wr_reg_n_0_[1] ),
        .I3(\bit_cntr_wr_reg_n_0_[2] ),
        .I4(\bit_cntr_wr_reg_n_0_[4] ),
        .O(rx_valid_i_2_n_0));
  FDCE #(
    .INIT(1'b0)) 
    rx_valid_reg
       (.C(CLK),
        .CE(\<const1> ),
        .CLR(rx_valid_reg_0),
        .D(rx_valid_i_1_n_0),
        .Q(rx_valid));
  LUT3 #(
    .INIT(8'h80)) 
    tx_valid_i_1
       (.I0(rx_data[9]),
        .I1(rx_data[8]),
        .I2(rst_n_IBUF),
        .O(tx_valid_reg));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT3 #(
    .INIT(8'h10)) 
    \wr_addr[7]_i_1 
       (.I0(rx_data[9]),
        .I1(rx_data[8]),
        .I2(rx_valid),
        .O(E));
endmodule
