module SPI_Wrapper_ref(SPI_Wrapper_ref_if.DUT intr);

	wire rx_valid, tx_valid;
	wire [intr.ADDR_SIZE+1:0] rx_data;
	wire [intr.ADDR_SIZE-1:0] tx_data;

	slave_ref_if #(intr.ADDR_SIZE) s1_ref (intr.clk);
	ram_ref_if #(.ADDR_SIZE(intr.ADDR_SIZE), .MEM_DEPTH(intr.MEM_DEPTH)) r1_ref (intr.clk);
endmodule