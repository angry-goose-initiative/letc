/*
 * File:    coraz7_top.sv
 * Brief:   Top wrapper for LETC on the Cora Z7
 *
 * Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Instanciates both LETC and the Zynq 7000 PS7 IP and connects everything as appropriate
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module coraz7_top (
    //Cora Z7 PL-Connected IO
    //These are PL controlled
    input  logic            i_raw_125mhz_clk,//Used only for debugging; FCLK from the PS7 is used for the main clock for LETC
    input  logic [1:0]      btn,
    output logic            led0_r,
    output logic            led0_g,
    output logic            led0_b,
    output logic            led1_r,
    output logic            led1_g,
    output logic            led1_b,
    //output logic            debug,//TODO

    //Cora Z7 PS-Connected IO
    //These AREN'T actually routed through the PL even though it looks like it here!
    //These are rather dedicated pins on the Zynq 7000 SoC for the PS
    inout  logic [53:0]     MIO,
    inout  logic            DDR_CAS_n,
    inout  logic            DDR_CKE,
    inout  logic            DDR_Clk_n,
    inout  logic            DDR_Clk,
    inout  logic            DDR_CS_n,
    inout  logic            DDR_DRSTB,
    inout  logic            DDR_ODT,
    inout  logic            DDR_RAS_n,
    inout  logic            DDR_WEB,
    inout  logic [2:0]      DDR_BankAddr,
    inout  logic [14:0]     DDR_Addr,
    inout  logic            DDR_VRN,
    inout  logic            DDR_VRP,
    inout  logic [3:0]      DDR_DM,
    inout  logic [31:0]     DDR_DQ,
    inout  logic [3:0]      DDR_DQS_n,
    inout  logic [3:0]      DDR_DQS,
    inout  logic            PS_SRSTB,
    inout  logic            PS_CLK,
    inout  logic            PS_PORB
);

/* ------------------------------------------------------------------------------------------------
 * LETC Top Instantiation
 * --------------------------------------------------------------------------------------------- */

logic letc_clk;
logic letc_rst_n;

logic [1:0] letc_btn;
logic       letc_led0_r;
logic       letc_led0_g;
logic       letc_led0_b;
logic       letc_led1_r;
logic       letc_led1_g;
logic       letc_led1_b;

logic                   letc_uart1_interrupt;
axi_if                  letc_axi_m_gp_0(.i_aclk(letc_clk), .i_arst_n(letc_rst_n));//LETC is the subordinate, PS is the manager
axi_if                  letc_axi_s_gp_0(.i_aclk(letc_clk), .i_arst_n(letc_rst_n));//PS is the subordinate, LETC is the manager
axi_if #(.DWIDTH(64))   letc_axi_s_acp(.i_aclk(letc_clk), .i_arst_n(letc_rst_n)); //PS is the subordinate, LETC is the manager

logic [7:0] letc_debug;

letc_top letc (
    //Clock and reset
    .i_clk(letc_clk),
    .i_rst_n(letc_rst_n),

    //LEDs and Buttons
    .i_btn(letc_btn),
    .o_led0_r(letc_led0_r),
    .o_led0_g(letc_led0_g),
    .o_led0_b(letc_led0_b),
    .o_led1_r(letc_led1_r),
    .o_led1_g(letc_led1_g),
    .o_led1_b(letc_led1_b),

    //PS Connections
    .i_uart1_interrupt(letc_uart1_interrupt),
    .axi_m_gp_0(letc_axi_m_gp_0),
    .axi_s_gp_0(letc_axi_s_gp_0),
    .axi_s_acp(letc_axi_s_acp),

    //Debug (Logic Analyzer)
    .o_debug(letc_debug)

    //TODO others
);

/* ------------------------------------------------------------------------------------------------
 * Zync 7000 PS7 IP Instantiation
 * --------------------------------------------------------------------------------------------- */

//I wasn't able to disable these USB0 signals in the IP configurator... not sure what they're for.
//Given we're not using USB for LETC anyways I think we'll just tie the inputs then
logic [1:0] USB0_PORT_INDCTL;
logic       USB0_VBUS_PWRSELECT;
logic       USB0_VBUS_PWRFAULT;
assign USB0_VBUS_PWRFAULT = 1'b0;

//M_AXI_GP0. The GP port where the PS is the manager and the PL is the subordinate
logic           M_AXI_GP0_ARVALID;
logic           M_AXI_GP0_AWVALID;
logic           M_AXI_GP0_BREADY;
logic           M_AXI_GP0_RREADY;
logic           M_AXI_GP0_WLAST;
logic           M_AXI_GP0_WVALID;
logic [11:0]    M_AXI_GP0_ARID;
logic [11:0]    M_AXI_GP0_AWID;
logic [11:0]    M_AXI_GP0_WID;
logic [1:0]     M_AXI_GP0_ARBURST;
logic [1:0]     M_AXI_GP0_ARLOCK;
logic [2:0]     M_AXI_GP0_ARSIZE;
logic [1:0]     M_AXI_GP0_AWBURST;
logic [1:0]     M_AXI_GP0_AWLOCK;
logic [2:0]     M_AXI_GP0_AWSIZE;
logic [2:0]     M_AXI_GP0_ARPROT;
logic [2:0]     M_AXI_GP0_AWPROT;
logic [31:0]    M_AXI_GP0_ARADDR;
logic [31:0]    M_AXI_GP0_AWADDR;
logic [31:0]    M_AXI_GP0_WDATA;
logic [3:0]     M_AXI_GP0_ARCACHE;
logic [3:0]     M_AXI_GP0_ARLEN;
logic [3:0]     M_AXI_GP0_ARQOS;
logic [3:0]     M_AXI_GP0_AWCACHE;
logic [3:0]     M_AXI_GP0_AWLEN;
logic [3:0]     M_AXI_GP0_AWQOS;
logic [3:0]     M_AXI_GP0_WSTRB;
logic           M_AXI_GP0_ACLK;
logic           M_AXI_GP0_ARREADY;
logic           M_AXI_GP0_AWREADY;
logic           M_AXI_GP0_BVALID;
logic           M_AXI_GP0_RLAST;
logic           M_AXI_GP0_RVALID;
logic           M_AXI_GP0_WREADY;
logic [11:0]    M_AXI_GP0_BID;
logic [11:0]    M_AXI_GP0_RID;
logic [1:0]     M_AXI_GP0_BRESP;
logic [1:0]     M_AXI_GP0_RRESP;
logic [31:0]    M_AXI_GP0_RDATA;

//S_AXI_GP0. The GP port where the PL is the manager and the PS is the subordinate.
logic           S_AXI_GP0_ARREADY;
logic           S_AXI_GP0_AWREADY;
logic           S_AXI_GP0_BVALID;
logic           S_AXI_GP0_RLAST;
logic           S_AXI_GP0_RVALID;
logic           S_AXI_GP0_WREADY;
logic [1:0]     S_AXI_GP0_BRESP;
logic [1:0]     S_AXI_GP0_RRESP;
logic [31:0]    S_AXI_GP0_RDATA;
logic [5:0]     S_AXI_GP0_BID;
logic [5:0]     S_AXI_GP0_RID;
logic           S_AXI_GP0_ACLK;
logic           S_AXI_GP0_ARVALID;
logic           S_AXI_GP0_AWVALID;
logic           S_AXI_GP0_BREADY;
logic           S_AXI_GP0_RREADY;
logic           S_AXI_GP0_WLAST;
logic           S_AXI_GP0_WVALID;
logic [1:0]     S_AXI_GP0_ARBURST;
logic [1:0]     S_AXI_GP0_ARLOCK;
logic [2:0]     S_AXI_GP0_ARSIZE;
logic [1:0]     S_AXI_GP0_AWBURST;
logic [1:0]     S_AXI_GP0_AWLOCK;
logic [2:0]     S_AXI_GP0_AWSIZE;
logic [2:0]     S_AXI_GP0_ARPROT;
logic [2:0]     S_AXI_GP0_AWPROT;
logic [31:0]    S_AXI_GP0_ARADDR;
logic [31:0]    S_AXI_GP0_AWADDR;
logic [31:0]    S_AXI_GP0_WDATA;
logic [3:0]     S_AXI_GP0_ARCACHE;
logic [3:0]     S_AXI_GP0_ARLEN;
logic [3:0]     S_AXI_GP0_ARQOS;
logic [3:0]     S_AXI_GP0_AWCACHE;
logic [3:0]     S_AXI_GP0_AWLEN;
logic [3:0]     S_AXI_GP0_AWQOS;
logic [3:0]     S_AXI_GP0_WSTRB;
logic [5:0]     S_AXI_GP0_ARID;
logic [5:0]     S_AXI_GP0_AWID;
logic [5:0]     S_AXI_GP0_WID;

//S_AXI_ACP. A speedy AXI port, backed by the ARM's L2. The PL is the manager and the PS is the subordinate.
logic           S_AXI_ACP_ARREADY;
logic           S_AXI_ACP_AWREADY;
logic           S_AXI_ACP_BVALID;
logic           S_AXI_ACP_RLAST;
logic           S_AXI_ACP_RVALID;
logic           S_AXI_ACP_WREADY;
logic [1:0]     S_AXI_ACP_BRESP;
logic [1:0]     S_AXI_ACP_RRESP;
logic [63:0]    S_AXI_ACP_RDATA;
logic [2:0]     S_AXI_ACP_BID;
logic [2:0]     S_AXI_ACP_RID;
logic           S_AXI_ACP_ACLK;
logic           S_AXI_ACP_ARVALID;
logic           S_AXI_ACP_AWVALID;
logic           S_AXI_ACP_BREADY;
logic           S_AXI_ACP_RREADY;
logic           S_AXI_ACP_WLAST;
logic           S_AXI_ACP_WVALID;
logic [2:0]     S_AXI_ACP_ARID;
logic [2:0]     S_AXI_ACP_ARPROT;
logic [2:0]     S_AXI_ACP_AWID;
logic [2:0]     S_AXI_ACP_AWPROT;
logic [2:0]     S_AXI_ACP_WID;
logic [31:0]    S_AXI_ACP_ARADDR;
logic [31:0]    S_AXI_ACP_AWADDR;
logic [3:0]     S_AXI_ACP_ARCACHE;
logic [3:0]     S_AXI_ACP_ARLEN;
logic [3:0]     S_AXI_ACP_ARQOS;
logic [3:0]     S_AXI_ACP_AWCACHE;
logic [3:0]     S_AXI_ACP_AWLEN;
logic [3:0]     S_AXI_ACP_AWQOS;
logic [1:0]     S_AXI_ACP_ARBURST;
logic [1:0]     S_AXI_ACP_ARLOCK;
logic [2:0]     S_AXI_ACP_ARSIZE;
logic [1:0]     S_AXI_ACP_AWBURST;
logic [1:0]     S_AXI_ACP_AWLOCK;
logic [2:0]     S_AXI_ACP_AWSIZE;
logic [4:0]     S_AXI_ACP_ARUSER;
logic [4:0]     S_AXI_ACP_AWUSER;
logic [63:0]    S_AXI_ACP_WDATA;
logic [7:0]     S_AXI_ACP_WSTRB;

//UART1 interrupt from the PS to the PL
logic IRQ_P2F_UART1;

//FCLK_CLK0 and FCLK_RESET0_N, software controllable clock and reset for LETC
logic FCLK_CLK0;
logic FCLK_RESET0_N;

//Based on the auto-generated instanciation template!
letc_ps7 ps (
    .USB0_PORT_INDCTL(USB0_PORT_INDCTL),        // output wire [1 : 0] USB0_PORT_INDCTL
    .USB0_VBUS_PWRSELECT(USB0_VBUS_PWRSELECT),  // output wire USB0_VBUS_PWRSELECT
    .USB0_VBUS_PWRFAULT(USB0_VBUS_PWRFAULT),    // input wire USB0_VBUS_PWRFAULT
    .M_AXI_GP0_ARVALID(M_AXI_GP0_ARVALID),      // output wire M_AXI_GP0_ARVALID
    .M_AXI_GP0_AWVALID(M_AXI_GP0_AWVALID),      // output wire M_AXI_GP0_AWVALID
    .M_AXI_GP0_BREADY(M_AXI_GP0_BREADY),        // output wire M_AXI_GP0_BREADY
    .M_AXI_GP0_RREADY(M_AXI_GP0_RREADY),        // output wire M_AXI_GP0_RREADY
    .M_AXI_GP0_WLAST(M_AXI_GP0_WLAST),          // output wire M_AXI_GP0_WLAST
    .M_AXI_GP0_WVALID(M_AXI_GP0_WVALID),        // output wire M_AXI_GP0_WVALID
    .M_AXI_GP0_ARID(M_AXI_GP0_ARID),            // output wire [11 : 0] M_AXI_GP0_ARID
    .M_AXI_GP0_AWID(M_AXI_GP0_AWID),            // output wire [11 : 0] M_AXI_GP0_AWID
    .M_AXI_GP0_WID(M_AXI_GP0_WID),              // output wire [11 : 0] M_AXI_GP0_WID
    .M_AXI_GP0_ARBURST(M_AXI_GP0_ARBURST),      // output wire [1 : 0] M_AXI_GP0_ARBURST
    .M_AXI_GP0_ARLOCK(M_AXI_GP0_ARLOCK),        // output wire [1 : 0] M_AXI_GP0_ARLOCK
    .M_AXI_GP0_ARSIZE(M_AXI_GP0_ARSIZE),        // output wire [2 : 0] M_AXI_GP0_ARSIZE
    .M_AXI_GP0_AWBURST(M_AXI_GP0_AWBURST),      // output wire [1 : 0] M_AXI_GP0_AWBURST
    .M_AXI_GP0_AWLOCK(M_AXI_GP0_AWLOCK),        // output wire [1 : 0] M_AXI_GP0_AWLOCK
    .M_AXI_GP0_AWSIZE(M_AXI_GP0_AWSIZE),        // output wire [2 : 0] M_AXI_GP0_AWSIZE
    .M_AXI_GP0_ARPROT(M_AXI_GP0_ARPROT),        // output wire [2 : 0] M_AXI_GP0_ARPROT
    .M_AXI_GP0_AWPROT(M_AXI_GP0_AWPROT),        // output wire [2 : 0] M_AXI_GP0_AWPROT
    .M_AXI_GP0_ARADDR(M_AXI_GP0_ARADDR),        // output wire [31 : 0] M_AXI_GP0_ARADDR
    .M_AXI_GP0_AWADDR(M_AXI_GP0_AWADDR),        // output wire [31 : 0] M_AXI_GP0_AWADDR
    .M_AXI_GP0_WDATA(M_AXI_GP0_WDATA),          // output wire [31 : 0] M_AXI_GP0_WDATA
    .M_AXI_GP0_ARCACHE(M_AXI_GP0_ARCACHE),      // output wire [3 : 0] M_AXI_GP0_ARCACHE
    .M_AXI_GP0_ARLEN(M_AXI_GP0_ARLEN),          // output wire [3 : 0] M_AXI_GP0_ARLEN
    .M_AXI_GP0_ARQOS(M_AXI_GP0_ARQOS),          // output wire [3 : 0] M_AXI_GP0_ARQOS
    .M_AXI_GP0_AWCACHE(M_AXI_GP0_AWCACHE),      // output wire [3 : 0] M_AXI_GP0_AWCACHE
    .M_AXI_GP0_AWLEN(M_AXI_GP0_AWLEN),          // output wire [3 : 0] M_AXI_GP0_AWLEN
    .M_AXI_GP0_AWQOS(M_AXI_GP0_AWQOS),          // output wire [3 : 0] M_AXI_GP0_AWQOS
    .M_AXI_GP0_WSTRB(M_AXI_GP0_WSTRB),          // output wire [3 : 0] M_AXI_GP0_WSTRB
    .M_AXI_GP0_ACLK(M_AXI_GP0_ACLK),            // input wire M_AXI_GP0_ACLK
    .M_AXI_GP0_ARREADY(M_AXI_GP0_ARREADY),      // input wire M_AXI_GP0_ARREADY
    .M_AXI_GP0_AWREADY(M_AXI_GP0_AWREADY),      // input wire M_AXI_GP0_AWREADY
    .M_AXI_GP0_BVALID(M_AXI_GP0_BVALID),        // input wire M_AXI_GP0_BVALID
    .M_AXI_GP0_RLAST(M_AXI_GP0_RLAST),          // input wire M_AXI_GP0_RLAST
    .M_AXI_GP0_RVALID(M_AXI_GP0_RVALID),        // input wire M_AXI_GP0_RVALID
    .M_AXI_GP0_WREADY(M_AXI_GP0_WREADY),        // input wire M_AXI_GP0_WREADY
    .M_AXI_GP0_BID(M_AXI_GP0_BID),              // input wire [11 : 0] M_AXI_GP0_BID
    .M_AXI_GP0_RID(M_AXI_GP0_RID),              // input wire [11 : 0] M_AXI_GP0_RID
    .M_AXI_GP0_BRESP(M_AXI_GP0_BRESP),          // input wire [1 : 0] M_AXI_GP0_BRESP
    .M_AXI_GP0_RRESP(M_AXI_GP0_RRESP),          // input wire [1 : 0] M_AXI_GP0_RRESP
    .M_AXI_GP0_RDATA(M_AXI_GP0_RDATA),          // input wire [31 : 0] M_AXI_GP0_RDATA
    .S_AXI_GP0_ARREADY(S_AXI_GP0_ARREADY),      // output wire S_AXI_GP0_ARREADY
    .S_AXI_GP0_AWREADY(S_AXI_GP0_AWREADY),      // output wire S_AXI_GP0_AWREADY
    .S_AXI_GP0_BVALID(S_AXI_GP0_BVALID),        // output wire S_AXI_GP0_BVALID
    .S_AXI_GP0_RLAST(S_AXI_GP0_RLAST),          // output wire S_AXI_GP0_RLAST
    .S_AXI_GP0_RVALID(S_AXI_GP0_RVALID),        // output wire S_AXI_GP0_RVALID
    .S_AXI_GP0_WREADY(S_AXI_GP0_WREADY),        // output wire S_AXI_GP0_WREADY
    .S_AXI_GP0_BRESP(S_AXI_GP0_BRESP),          // output wire [1 : 0] S_AXI_GP0_BRESP
    .S_AXI_GP0_RRESP(S_AXI_GP0_RRESP),          // output wire [1 : 0] S_AXI_GP0_RRESP
    .S_AXI_GP0_RDATA(S_AXI_GP0_RDATA),          // output wire [31 : 0] S_AXI_GP0_RDATA
    .S_AXI_GP0_BID(S_AXI_GP0_BID),              // output wire [5 : 0] S_AXI_GP0_BID
    .S_AXI_GP0_RID(S_AXI_GP0_RID),              // output wire [5 : 0] S_AXI_GP0_RID
    .S_AXI_GP0_ACLK(S_AXI_GP0_ACLK),            // input wire S_AXI_GP0_ACLK
    .S_AXI_GP0_ARVALID(S_AXI_GP0_ARVALID),      // input wire S_AXI_GP0_ARVALID
    .S_AXI_GP0_AWVALID(S_AXI_GP0_AWVALID),      // input wire S_AXI_GP0_AWVALID
    .S_AXI_GP0_BREADY(S_AXI_GP0_BREADY),        // input wire S_AXI_GP0_BREADY
    .S_AXI_GP0_RREADY(S_AXI_GP0_RREADY),        // input wire S_AXI_GP0_RREADY
    .S_AXI_GP0_WLAST(S_AXI_GP0_WLAST),          // input wire S_AXI_GP0_WLAST
    .S_AXI_GP0_WVALID(S_AXI_GP0_WVALID),        // input wire S_AXI_GP0_WVALID
    .S_AXI_GP0_ARBURST(S_AXI_GP0_ARBURST),      // input wire [1 : 0] S_AXI_GP0_ARBURST
    .S_AXI_GP0_ARLOCK(S_AXI_GP0_ARLOCK),        // input wire [1 : 0] S_AXI_GP0_ARLOCK
    .S_AXI_GP0_ARSIZE(S_AXI_GP0_ARSIZE),        // input wire [2 : 0] S_AXI_GP0_ARSIZE
    .S_AXI_GP0_AWBURST(S_AXI_GP0_AWBURST),      // input wire [1 : 0] S_AXI_GP0_AWBURST
    .S_AXI_GP0_AWLOCK(S_AXI_GP0_AWLOCK),        // input wire [1 : 0] S_AXI_GP0_AWLOCK
    .S_AXI_GP0_AWSIZE(S_AXI_GP0_AWSIZE),        // input wire [2 : 0] S_AXI_GP0_AWSIZE
    .S_AXI_GP0_ARPROT(S_AXI_GP0_ARPROT),        // input wire [2 : 0] S_AXI_GP0_ARPROT
    .S_AXI_GP0_AWPROT(S_AXI_GP0_AWPROT),        // input wire [2 : 0] S_AXI_GP0_AWPROT
    .S_AXI_GP0_ARADDR(S_AXI_GP0_ARADDR),        // input wire [31 : 0] S_AXI_GP0_ARADDR
    .S_AXI_GP0_AWADDR(S_AXI_GP0_AWADDR),        // input wire [31 : 0] S_AXI_GP0_AWADDR
    .S_AXI_GP0_WDATA(S_AXI_GP0_WDATA),          // input wire [31 : 0] S_AXI_GP0_WDATA
    .S_AXI_GP0_ARCACHE(S_AXI_GP0_ARCACHE),      // input wire [3 : 0] S_AXI_GP0_ARCACHE
    .S_AXI_GP0_ARLEN(S_AXI_GP0_ARLEN),          // input wire [3 : 0] S_AXI_GP0_ARLEN
    .S_AXI_GP0_ARQOS(S_AXI_GP0_ARQOS),          // input wire [3 : 0] S_AXI_GP0_ARQOS
    .S_AXI_GP0_AWCACHE(S_AXI_GP0_AWCACHE),      // input wire [3 : 0] S_AXI_GP0_AWCACHE
    .S_AXI_GP0_AWLEN(S_AXI_GP0_AWLEN),          // input wire [3 : 0] S_AXI_GP0_AWLEN
    .S_AXI_GP0_AWQOS(S_AXI_GP0_AWQOS),          // input wire [3 : 0] S_AXI_GP0_AWQOS
    .S_AXI_GP0_WSTRB(S_AXI_GP0_WSTRB),          // input wire [3 : 0] S_AXI_GP0_WSTRB
    .S_AXI_GP0_ARID(S_AXI_GP0_ARID),            // input wire [5 : 0] S_AXI_GP0_ARID
    .S_AXI_GP0_AWID(S_AXI_GP0_AWID),            // input wire [5 : 0] S_AXI_GP0_AWID
    .S_AXI_GP0_WID(S_AXI_GP0_WID),              // input wire [5 : 0] S_AXI_GP0_WID
    .S_AXI_ACP_ARREADY(S_AXI_ACP_ARREADY),      // output wire S_AXI_ACP_ARREADY
    .S_AXI_ACP_AWREADY(S_AXI_ACP_AWREADY),      // output wire S_AXI_ACP_AWREADY
    .S_AXI_ACP_BVALID(S_AXI_ACP_BVALID),        // output wire S_AXI_ACP_BVALID
    .S_AXI_ACP_RLAST(S_AXI_ACP_RLAST),          // output wire S_AXI_ACP_RLAST
    .S_AXI_ACP_RVALID(S_AXI_ACP_RVALID),        // output wire S_AXI_ACP_RVALID
    .S_AXI_ACP_WREADY(S_AXI_ACP_WREADY),        // output wire S_AXI_ACP_WREADY
    .S_AXI_ACP_BRESP(S_AXI_ACP_BRESP),          // output wire [1 : 0] S_AXI_ACP_BRESP
    .S_AXI_ACP_RRESP(S_AXI_ACP_RRESP),          // output wire [1 : 0] S_AXI_ACP_RRESP
    .S_AXI_ACP_BID(S_AXI_ACP_BID),              // output wire [2 : 0] S_AXI_ACP_BID
    .S_AXI_ACP_RID(S_AXI_ACP_RID),              // output wire [2 : 0] S_AXI_ACP_RID
    .S_AXI_ACP_RDATA(S_AXI_ACP_RDATA),          // output wire [63 : 0] S_AXI_ACP_RDATA
    .S_AXI_ACP_ACLK(S_AXI_ACP_ACLK),            // input wire S_AXI_ACP_ACLK
    .S_AXI_ACP_ARVALID(S_AXI_ACP_ARVALID),      // input wire S_AXI_ACP_ARVALID
    .S_AXI_ACP_AWVALID(S_AXI_ACP_AWVALID),      // input wire S_AXI_ACP_AWVALID
    .S_AXI_ACP_BREADY(S_AXI_ACP_BREADY),        // input wire S_AXI_ACP_BREADY
    .S_AXI_ACP_RREADY(S_AXI_ACP_RREADY),        // input wire S_AXI_ACP_RREADY
    .S_AXI_ACP_WLAST(S_AXI_ACP_WLAST),          // input wire S_AXI_ACP_WLAST
    .S_AXI_ACP_WVALID(S_AXI_ACP_WVALID),        // input wire S_AXI_ACP_WVALID
    .S_AXI_ACP_ARID(S_AXI_ACP_ARID),            // input wire [2 : 0] S_AXI_ACP_ARID
    .S_AXI_ACP_ARPROT(S_AXI_ACP_ARPROT),        // input wire [2 : 0] S_AXI_ACP_ARPROT
    .S_AXI_ACP_AWID(S_AXI_ACP_AWID),            // input wire [2 : 0] S_AXI_ACP_AWID
    .S_AXI_ACP_AWPROT(S_AXI_ACP_AWPROT),        // input wire [2 : 0] S_AXI_ACP_AWPROT
    .S_AXI_ACP_WID(S_AXI_ACP_WID),              // input wire [2 : 0] S_AXI_ACP_WID
    .S_AXI_ACP_ARADDR(S_AXI_ACP_ARADDR),        // input wire [31 : 0] S_AXI_ACP_ARADDR
    .S_AXI_ACP_AWADDR(S_AXI_ACP_AWADDR),        // input wire [31 : 0] S_AXI_ACP_AWADDR
    .S_AXI_ACP_ARCACHE(S_AXI_ACP_ARCACHE),      // input wire [3 : 0] S_AXI_ACP_ARCACHE
    .S_AXI_ACP_ARLEN(S_AXI_ACP_ARLEN),          // input wire [3 : 0] S_AXI_ACP_ARLEN
    .S_AXI_ACP_ARQOS(S_AXI_ACP_ARQOS),          // input wire [3 : 0] S_AXI_ACP_ARQOS
    .S_AXI_ACP_AWCACHE(S_AXI_ACP_AWCACHE),      // input wire [3 : 0] S_AXI_ACP_AWCACHE
    .S_AXI_ACP_AWLEN(S_AXI_ACP_AWLEN),          // input wire [3 : 0] S_AXI_ACP_AWLEN
    .S_AXI_ACP_AWQOS(S_AXI_ACP_AWQOS),          // input wire [3 : 0] S_AXI_ACP_AWQOS
    .S_AXI_ACP_ARBURST(S_AXI_ACP_ARBURST),      // input wire [1 : 0] S_AXI_ACP_ARBURST
    .S_AXI_ACP_ARLOCK(S_AXI_ACP_ARLOCK),        // input wire [1 : 0] S_AXI_ACP_ARLOCK
    .S_AXI_ACP_ARSIZE(S_AXI_ACP_ARSIZE),        // input wire [2 : 0] S_AXI_ACP_ARSIZE
    .S_AXI_ACP_AWBURST(S_AXI_ACP_AWBURST),      // input wire [1 : 0] S_AXI_ACP_AWBURST
    .S_AXI_ACP_AWLOCK(S_AXI_ACP_AWLOCK),        // input wire [1 : 0] S_AXI_ACP_AWLOCK
    .S_AXI_ACP_AWSIZE(S_AXI_ACP_AWSIZE),        // input wire [2 : 0] S_AXI_ACP_AWSIZE
    .S_AXI_ACP_ARUSER(S_AXI_ACP_ARUSER),        // input wire [4 : 0] S_AXI_ACP_ARUSER
    .S_AXI_ACP_AWUSER(S_AXI_ACP_AWUSER),        // input wire [4 : 0] S_AXI_ACP_AWUSER
    .S_AXI_ACP_WDATA(S_AXI_ACP_WDATA),          // input wire [63 : 0] S_AXI_ACP_WDATA
    .S_AXI_ACP_WSTRB(S_AXI_ACP_WSTRB),          // input wire [7 : 0] S_AXI_ACP_WSTRB
    .IRQ_P2F_UART1(IRQ_P2F_UART1),              // output wire IRQ_P2F_UART1
    .FCLK_CLK0(FCLK_CLK0),                      // output wire FCLK_CLK0
    .FCLK_RESET0_N(FCLK_RESET0_N),              // output wire FCLK_RESET0_N
    .MIO(MIO),                                  // inout wire [53 : 0] MIO
    .DDR_CAS_n(DDR_CAS_n),                      // inout wire DDR_CAS_n
    .DDR_CKE(DDR_CKE),                          // inout wire DDR_CKE
    .DDR_Clk_n(DDR_Clk_n),                      // inout wire DDR_Clk_n
    .DDR_Clk(DDR_Clk),                          // inout wire DDR_Clk
    .DDR_CS_n(DDR_CS_n),                        // inout wire DDR_CS_n
    .DDR_DRSTB(DDR_DRSTB),                      // inout wire DDR_DRSTB
    .DDR_ODT(DDR_ODT),                          // inout wire DDR_ODT
    .DDR_RAS_n(DDR_RAS_n),                      // inout wire DDR_RAS_n
    .DDR_WEB(DDR_WEB),                          // inout wire DDR_WEB
    .DDR_BankAddr(DDR_BankAddr),                // inout wire [2 : 0] DDR_BankAddr
    .DDR_Addr(DDR_Addr),                        // inout wire [14 : 0] DDR_Addr
    .DDR_VRN(DDR_VRN),                          // inout wire DDR_VRN
    .DDR_VRP(DDR_VRP),                          // inout wire DDR_VRP
    .DDR_DM(DDR_DM),                            // inout wire [3 : 0] DDR_DM
    .DDR_DQ(DDR_DQ),                            // inout wire [31 : 0] DDR_DQ
    .DDR_DQS_n(DDR_DQS_n),                      // inout wire [3 : 0] DDR_DQS_n
    .DDR_DQS(DDR_DQS),                          // inout wire [3 : 0] DDR_DQS
    .PS_SRSTB(PS_SRSTB),                        // inout wire PS_SRSTB
    .PS_CLK(PS_CLK),                            // inout wire PS_CLK
    .PS_PORB(PS_PORB)                           // inout wire PS_PORB
);

/* ------------------------------------------------------------------------------------------------
 * Synchronizers
 * --------------------------------------------------------------------------------------------- */

//The UART1 interrupt from the PS to the PL is asynchronous to the FCLKs
logic uart1_interrupt_sync;
cdc_synchronizer #(
    .WIDTH(1)
) uart1_synchronizer (
    .i_clk(letc_clk),
    .i_async_data(IRQ_P2F_UART1),
    .o_sync_data(uart1_interrupt_sync)
);

//Same goes for the software controllable reset
logic FCLK_RESET0_N_sync;
cdc_synchronizer #(
    .WIDTH(1)
) reset_synchronizer (
    .i_clk(letc_clk),
    .i_async_data(FCLK_RESET0_N),
    .o_sync_data(FCLK_RESET0_N_sync)
);

//Buttons
logic [1:0] btn_sync;
cdc_synchronizer #(
    .WIDTH(2)
) btn_synchronizer (
    .i_clk(letc_clk),
    .i_async_data(btn),
    .o_sync_data(btn_sync)
);

//Not really needed for LEDs, but the flops will help with timing
logic led0_r_pre_sync;
logic led0_g_pre_sync;
logic led0_b_pre_sync;
logic led1_r_pre_sync;
logic led1_g_pre_sync;
logic led1_b_pre_sync;
cdc_synchronizer #(
    .WIDTH(6)
) led_synchronizer (
    .i_clk(letc_clk),
    .i_async_data({led0_r_pre_sync, led0_g_pre_sync, led0_b_pre_sync, led1_r_pre_sync, led1_g_pre_sync, led1_b_pre_sync}),
    .o_sync_data({led0_r, led0_g, led0_b, led1_r, led1_g, led1_b})
);

/* ------------------------------------------------------------------------------------------------
 * Connections Between LETC and PS7
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    letc_clk    = FCLK_CLK0;
    letc_rst_n  = FCLK_RESET0_N_sync;

    //Useful for debugging without the PS7 running
    //letc_clk    = i_raw_125mhz_clk;
    //letc_rst_n  = ~btn_sync[0];

end

always_comb begin
    letc_btn = btn_sync;

    led0_r_pre_sync = letc_led0_r;
    led0_g_pre_sync = letc_led0_g;
    led0_b_pre_sync = letc_led0_b;
    led1_r_pre_sync = letc_led1_r;
    led1_g_pre_sync = letc_led1_g;
    led1_b_pre_sync = letc_led1_b;
end

always_comb begin
    letc_uart1_interrupt = uart1_interrupt_sync;

    //M_AXI_GP0. The GP port where the PS is the manager and the PL is the subordinate
    //AxPROT, AxCACHE, AxLOCK, and AxQOS are ignored
    M_AXI_GP0_ACLK = letc_clk;

    letc_axi_m_gp_0.awvalid = M_AXI_GP0_AWVALID;
    M_AXI_GP0_AWREADY       = letc_axi_m_gp_0.awready;
    letc_axi_m_gp_0.awaddr  = M_AXI_GP0_AWADDR;
    letc_axi_m_gp_0.awid    = M_AXI_GP0_AWID;
    letc_axi_m_gp_0.awlen   = M_AXI_GP0_AWLEN;
    letc_axi_m_gp_0.awsize  = M_AXI_GP0_AWSIZE;
    letc_axi_m_gp_0.awburst = M_AXI_GP0_AWBURST;

    letc_axi_m_gp_0.wvalid  = M_AXI_GP0_WVALID;
    M_AXI_GP0_WREADY        = letc_axi_m_gp_0.wready;
    letc_axi_m_gp_0.wid     = M_AXI_GP0_WID;
    letc_axi_m_gp_0.wdata   = M_AXI_GP0_WDATA;
    letc_axi_m_gp_0.wstrb   = M_AXI_GP0_WSTRB;
    letc_axi_m_gp_0.wlast   = M_AXI_GP0_WLAST;

    M_AXI_GP0_BVALID        = letc_axi_m_gp_0.bvalid;
    letc_axi_m_gp_0.bready  = M_AXI_GP0_BREADY;
    M_AXI_GP0_BID           = letc_axi_m_gp_0.bid;
    M_AXI_GP0_BRESP         = letc_axi_m_gp_0.bresp;

    letc_axi_m_gp_0.arvalid = M_AXI_GP0_ARVALID;
    M_AXI_GP0_ARREADY       = letc_axi_m_gp_0.arready;
    letc_axi_m_gp_0.araddr  = M_AXI_GP0_ARADDR;
    letc_axi_m_gp_0.arid    = M_AXI_GP0_ARID;
    letc_axi_m_gp_0.arlen   = M_AXI_GP0_ARLEN;
    letc_axi_m_gp_0.arsize  = M_AXI_GP0_ARSIZE;
    letc_axi_m_gp_0.arburst = M_AXI_GP0_ARBURST;

    M_AXI_GP0_RVALID        = letc_axi_m_gp_0.rvalid;
    letc_axi_m_gp_0.rready  = M_AXI_GP0_RREADY;
    M_AXI_GP0_RID           = letc_axi_m_gp_0.rid;
    M_AXI_GP0_RDATA         = letc_axi_m_gp_0.rdata;
    M_AXI_GP0_RRESP         = letc_axi_m_gp_0.rresp;
    M_AXI_GP0_RLAST         = letc_axi_m_gp_0.rlast;

    //S_AXI_GP0. The GP port where the PL is the manager and the PS is the subordinate.
    //AxPROT, AxCACHE, AxLOCK, and AxQOS are tied off
    S_AXI_GP0_AWPROT    = 3'b000;
    S_AXI_GP0_ARPROT    = 3'b000;
    S_AXI_GP0_AWCACHE   = 4'b0000;//Since we intend to use this port for I/O don't use any caching
    S_AXI_GP0_ARCACHE   = 4'b0000;//Since we intend to use this port for I/O don't use any caching
    S_AXI_GP0_AWLOCK    = 2'b00;
    S_AXI_GP0_ARLOCK    = 2'b00;
    S_AXI_GP0_AWQOS     = 4'b0000;
    S_AXI_GP0_ARQOS     = 4'b0000;

    S_AXI_GP0_ACLK = letc_clk;

    S_AXI_GP0_AWVALID       = letc_axi_s_gp_0.awvalid;
    letc_axi_s_gp_0.awready = S_AXI_GP0_AWREADY;
    S_AXI_GP0_AWADDR        = letc_axi_s_gp_0.awaddr;
    S_AXI_GP0_AWID          = letc_axi_s_gp_0.awid;
    S_AXI_GP0_AWLEN         = letc_axi_s_gp_0.awlen;
    S_AXI_GP0_AWSIZE        = letc_axi_s_gp_0.awsize;
    S_AXI_GP0_AWBURST       = letc_axi_s_gp_0.awburst;

    S_AXI_GP0_WVALID        = letc_axi_s_gp_0.wvalid;
    letc_axi_s_gp_0.wready  = S_AXI_GP0_WREADY;
    S_AXI_GP0_WID           = letc_axi_s_gp_0.wid;
    S_AXI_GP0_WDATA         = letc_axi_s_gp_0.wdata;
    S_AXI_GP0_WSTRB         = letc_axi_s_gp_0.wstrb;
    S_AXI_GP0_WLAST         = letc_axi_s_gp_0.wlast;

    letc_axi_s_gp_0.bvalid  = S_AXI_GP0_BVALID;
    S_AXI_GP0_BREADY        = letc_axi_s_gp_0.bready;
    letc_axi_s_gp_0.bid     = S_AXI_GP0_BID;
    letc_axi_s_gp_0.bresp   = S_AXI_GP0_BRESP;

    S_AXI_GP0_ARVALID       = letc_axi_s_gp_0.arvalid;
    letc_axi_s_gp_0.arready = S_AXI_GP0_ARREADY;
    S_AXI_GP0_ARADDR        = letc_axi_s_gp_0.araddr;
    S_AXI_GP0_ARID          = letc_axi_s_gp_0.arid;
    S_AXI_GP0_ARLEN         = letc_axi_s_gp_0.arlen;
    S_AXI_GP0_ARSIZE        = letc_axi_s_gp_0.arsize;
    S_AXI_GP0_ARBURST       = letc_axi_s_gp_0.arburst;

    letc_axi_s_gp_0.rvalid  = S_AXI_GP0_RVALID;
    S_AXI_GP0_RREADY        = letc_axi_s_gp_0.rready;
    letc_axi_s_gp_0.rid     = S_AXI_GP0_RID;
    letc_axi_s_gp_0.rdata   = S_AXI_GP0_RDATA;
    letc_axi_s_gp_0.rresp   = S_AXI_GP0_RRESP;
    letc_axi_s_gp_0.rlast   = S_AXI_GP0_RLAST;

    //S_AXI_ACP. A speedy AXI port, backed by the ARM's L2. The PL is the manager and the PS is the subordinate.
    //AxPROT, AxCACHE, AxLOCK, and AxQOS are tied off
    S_AXI_ACP_AWPROT    = 3'b000;
    S_AXI_ACP_ARPROT    = 3'b000;
    S_AXI_ACP_AWCACHE   = 4'b1111;//Since we intend to use this port for memory, allow all caching behavior
    S_AXI_ACP_ARCACHE   = 4'b1111;//Since we intend to use this port for memory, allow all caching behavior
    S_AXI_ACP_AWLOCK    = 2'b00;
    S_AXI_ACP_ARLOCK    = 2'b00;
    S_AXI_ACP_AWQOS     = 4'b0000;
    S_AXI_ACP_ARQOS     = 4'b0000;
    
    S_AXI_ACP_AWUSER    = 5'b11111;//TODO is this correct? Enable coherency
    S_AXI_ACP_ARUSER    = 5'b11111;//TODO is this correct? Enable coherency
    
    S_AXI_ACP_ACLK = letc_clk;

    S_AXI_ACP_AWVALID       = letc_axi_s_acp.awvalid;
    letc_axi_s_acp.awready  = S_AXI_ACP_AWREADY;
    S_AXI_ACP_AWADDR        = letc_axi_s_acp.awaddr;
    S_AXI_ACP_AWID          = letc_axi_s_acp.awid;
    S_AXI_ACP_AWLEN         = letc_axi_s_acp.awlen;
    S_AXI_ACP_AWSIZE        = letc_axi_s_acp.awsize;
    S_AXI_ACP_AWBURST       = letc_axi_s_acp.awburst;

    S_AXI_ACP_WVALID        = letc_axi_s_acp.wvalid;
    letc_axi_s_acp.wready   = S_AXI_ACP_WREADY;
    S_AXI_ACP_WID           = letc_axi_s_acp.wid;
    S_AXI_ACP_WDATA         = letc_axi_s_acp.wdata;
    S_AXI_ACP_WSTRB         = letc_axi_s_acp.wstrb;
    S_AXI_ACP_WLAST         = letc_axi_s_acp.wlast;

    letc_axi_s_acp.bvalid   = S_AXI_ACP_BVALID;
    S_AXI_ACP_BREADY        = letc_axi_s_acp.bready;
    letc_axi_s_acp.bid      = S_AXI_ACP_BID;
    letc_axi_s_acp.bresp    = S_AXI_ACP_BRESP;

    S_AXI_ACP_ARVALID       = letc_axi_s_acp.arvalid;
    letc_axi_s_acp.arready  = S_AXI_ACP_ARREADY;
    S_AXI_ACP_ARADDR        = letc_axi_s_acp.araddr;
    S_AXI_ACP_ARID          = letc_axi_s_acp.arid;
    S_AXI_ACP_ARLEN         = letc_axi_s_acp.arlen;
    S_AXI_ACP_ARSIZE        = letc_axi_s_acp.arsize;
    S_AXI_ACP_ARBURST       = letc_axi_s_acp.arburst;

    letc_axi_s_acp.rvalid   = S_AXI_ACP_RVALID;
    S_AXI_ACP_RREADY        = letc_axi_s_acp.rready;
    letc_axi_s_acp.rid      = S_AXI_ACP_RID;
    letc_axi_s_acp.rdata    = S_AXI_ACP_RDATA;
    letc_axi_s_acp.rresp    = S_AXI_ACP_RRESP;
    letc_axi_s_acp.rlast    = S_AXI_ACP_RLAST;
end

//assign debug = letc_debug;//TODO

//TESTING
/*
reg [31:0] fclk_counter;
always @(posedge FCLK_CLK0) begin
    fclk_counter <= fclk_counter + 1;
end
assign led0_r_sync = fclk_counter[24];
assign led0_g_sync = fclk_counter[31];//Timing test; can we do a 32-bit counter fast enough?
reg [31:0] counter;
always @(posedge i_raw_125mhz_clk) begin
    counter <= counter + 1;
end
assign led1_r_sync = counter[24];
assign led0_b_sync = btn_sync[0];
assign led1_b_sync = btn_sync[1];
*/

endmodule
