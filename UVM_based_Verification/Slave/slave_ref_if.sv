interface slave_ref_if (clk);

	parameter ADDR_SIZE = 8;

	input clk;
	bit MOSI, SS_n, rst_n, tx_valid, rx_valid_ref, MISO_ref;
	logic [ADDR_SIZE-1:0] tx_data;
	logic [ADDR_SIZE+1:0] rx_data_ref;


	modport DUT (output MISO_ref, rx_data_ref, rx_valid_ref,
					input clk, rst_n, SS_n, MOSI, tx_valid, tx_data);

endinterface : slave_ref_if