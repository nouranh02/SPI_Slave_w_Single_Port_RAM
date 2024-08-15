interface ram_if (clk);

	parameter MEM_DEPTH = 256;
	parameter ADDR_SIZE = 8;

	input clk;
	bit rst_n , rx_valid, tx_valid;
	logic [ADDR_SIZE-1:0] dout;
	logic [ADDR_SIZE+1:0] din;

	modport DUT (output tx_valid, dout,
					input clk, rst_n, rx_valid, din);
	
	modport TEST (output rst_n, rx_valid, din,
					input clk, tx_valid, dout);

endinterface : ram_if