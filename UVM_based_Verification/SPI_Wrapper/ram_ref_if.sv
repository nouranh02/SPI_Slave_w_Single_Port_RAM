interface ram_ref_if (clk);

	parameter MEM_DEPTH = 256;
	parameter ADDR_SIZE = 8;

	input clk;
	bit rst_n , rx_valid, tx_valid_ref;
	logic [ADDR_SIZE+1:0] din;
	logic [ADDR_SIZE-1:0] dout_ref;


	modport DUT (output tx_valid_ref, dout_ref,
					input clk, rst_n, rx_valid, din);

endinterface : ram_ref_if