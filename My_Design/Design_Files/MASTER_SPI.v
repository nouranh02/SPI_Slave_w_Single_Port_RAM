module MASTER_SPI(clk, rst_n, SS_n, MOSI, MISO);
	parameter ADDR_SIZE = 8;
	input clk, rst_n, SS_n, MOSI;
	output MISO;

	wire rx_valid, tx_valid;
	wire [ADDR_SIZE+1:0] rx_data;
	wire [ADDR_SIZE-1:0] tx_data;

	RAM #(.ADDR_SIZE(ADDR_SIZE)) RAM1(clk, rst_n, rx_valid, rx_data, tx_valid, tx_data);
	SPI_SLAVE #(.ADDR_SIZE(ADDR_SIZE)) SPI1(clk, rst_n, SS_n, MOSI, MISO, rx_data, rx_valid, tx_data, tx_valid);
endmodule