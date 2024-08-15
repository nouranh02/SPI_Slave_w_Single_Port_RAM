interface SPI_Wrapper_ref_if (clk);

	parameter ADDR_SIZE = 8;
	parameter MEM_DEPTH = 256;

	input clk;
	bit rst_n, SS_n, MOSI, MISO_ref;


	modport DUT (output MISO_ref,
					input clk, rst_n, SS_n, MOSI);

endinterface : SPI_Wrapper_ref_if