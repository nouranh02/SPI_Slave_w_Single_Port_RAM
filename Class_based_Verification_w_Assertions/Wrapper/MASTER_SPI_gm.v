module MASTER_SPI_gm(clk, rst_n, SS_n, MOSI, MISO);
	parameter ADDR_SIZE = 8;
	parameter MEM_DEPTH = 256;

	input clk, rst_n, SS_n, MOSI;
	output MISO;

	wire rx_valid, tx_valid;
	wire [ADDR_SIZE+1:0] rx_data;
	wire [ADDR_SIZE-1:0] tx_data;

	RAM_gm #(.ADDR_SIZE(ADDR_SIZE), .MEM_DEPTH(MEM_DEPTH)) RAM1(.clk(clk), .rst_n(rst_n), .rx_valid(rx_valid), .din(rx_data), .tx_valid(tx_valid), .dout(tx_data));
	SPI_SLAVE_gm #(.ADDR_SIZE(ADDR_SIZE)) SPI1(.clk(clk), .rst_n(rst_n), .SS_n(SS_n), .MOSI(MOSI), .MISO(MISO), .rx_data(rx_data), .rx_valid(rx_valid), .tx_data(tx_data), .tx_valid(tx_valid));
endmodule