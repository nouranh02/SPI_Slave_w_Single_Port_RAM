module SPI_Wrapper(SPI_Wrapper_if.DUT intr);

	////////////////////////////////////////////////////////////////////Original Code////////////////////////////////////////////////////////////////////
/*
	input MOSI,clk,rst_n,SS_n;
	output MISO;

	wire [7:0] tx_data1;
	wire tx_valid1,rx_valid1;
	wire [9:0] rx_data1;
	slave #(ADDR_SIZE) s1(.MOSI(MOSI),.SS_n(SS_n),.clk(clk),.rst_n(rst_n),.tx_valid(tx_valid1),.tx_data(tx_data1),.rx_data(rx_data1),.rx_valid(rx_valid1),.MISO(MISO));
	ram #(.ADDR_SIZE(ADDR_SIZE), .MEM_DEPTH(MEM_DEPTH)) r1(.din(rx_data1),.clk(clk),.rst_n(rst_n),.rx_valid(rx_valid1),.dout(tx_data1),.tx_valid(tx_valid1));
*/	
	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////Edited Code/////////////////////////////////////////////////////////////////////

	wire [intr.ADDR_SIZE-1:0] tx_data1;
	wire tx_valid1,rx_valid1;
	wire [intr.ADDR_SIZE+1:0] rx_data1;

	slave_if #(intr.ADDR_SIZE) s1 (intr.clk);
	ram_if #(.ADDR_SIZE(intr.ADDR_SIZE), .MEM_DEPTH(intr.MEM_DEPTH)) r1 (intr.clk);

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	`ifdef SIM
		property reset_asserted;
			@(posedge intr.clk)
			$fell(intr.rst_n) |=> ~intr.MISO;
		endproperty

		property SS_inactive;
			@(posedge intr.clk) disable iff(!intr.rst_n)
			$rose(intr.SS_n) |=> ~intr.MISO;
		endproperty

		property tx_inactive;
			@(posedge intr.clk) disable iff(!intr.rst_n)
			!tx_valid1 |=> ~intr.MISO;
		endproperty

		property MISO_out;
			int i = 0;
			@(posedge intr.clk) disable iff(!intr.rst_n || $rose(intr.SS_n, @(posedge intr.clk)))
			$fell(intr.SS_n) ##[intr.ADDR_SIZE:intr.ADDR_SIZE+5] $rose(tx_valid1) |=> ((intr.MISO == tx_data1[intr.ADDR_SIZE-1-i]), i++)[*(intr.ADDR_SIZE)];
		endproperty

		assertion_reset_asserted:	assert property(reset_asserted);
		cover_reset_asserted:	  	cover property(reset_asserted);

		assertion_SS_inactive:		assert property(SS_inactive);
		cover_SS_inactive:	  		cover property(SS_inactive);

		assertion_tx_inactive:		assert property(tx_inactive);
		cover_tx_inactive:			cover property(tx_inactive);

		assertion_MISO_out:			assert property(MISO_out);
		cover_SS_MISO_out:			cover property(MISO_out);
	`endif

endmodule