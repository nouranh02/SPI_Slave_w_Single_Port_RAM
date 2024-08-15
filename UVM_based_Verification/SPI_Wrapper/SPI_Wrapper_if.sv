interface SPI_Wrapper_if (clk);

	parameter ADDR_SIZE = 8;
	parameter MEM_DEPTH = 256;

	input clk;
	bit rst_n, SS_n, MOSI, MISO;


	modport DUT (output MISO,
					input clk, rst_n, SS_n, MOSI);

endinterface : SPI_Wrapper_if