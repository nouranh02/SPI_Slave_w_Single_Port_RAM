interface slave_if (clk);

	parameter ADDR_SIZE = 8;

	input clk;
	bit MOSI, SS_n, rst_n, tx_valid, rx_valid, MISO;
	logic [ADDR_SIZE-1:0] tx_data;
	logic [ADDR_SIZE+1:0] rx_data;


	modport DUT (output MISO, rx_data, rx_valid,
					input clk, rst_n, SS_n, MOSI, tx_valid, tx_data);
	
	modport TEST (output rst_n, SS_n, MOSI, tx_valid, tx_data,
					input clk, MISO, rx_data, rx_valid);

endinterface : slave_if