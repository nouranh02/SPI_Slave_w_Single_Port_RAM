module ram_ref (ram_ref_if.DUT intr);

	reg [intr.ADDR_SIZE-1:0] wr_addr, rd_addr;
	reg [intr.ADDR_SIZE-1:0] mem [intr.MEM_DEPTH-1:0];

	wire [1:0] signal;
	wire [intr.ADDR_SIZE-1:0] data;

	assign signal = intr.din[intr.ADDR_SIZE+1:intr.ADDR_SIZE];
    assign data = intr.din[intr.ADDR_SIZE-1:0];

	always @(posedge intr.clk or negedge intr.rst_n) begin
		if(~intr.rst_n) begin
			intr.dout_ref <= 0;
			intr.tx_valid_ref <= 0;
			wr_addr <= 0;
			rd_addr <= 0;
		end
		else if(intr.rx_valid) begin
			case (signal)
				2'b00: begin
					wr_addr <= data;
					intr.tx_valid_ref <=0;
				end
				2'b01: begin
					mem [wr_addr] <= data;
					intr.tx_valid_ref <=0;
				end	
				2'b10: begin
					rd_addr <= data;
					intr.tx_valid_ref <=0;
				end
				default: begin
					intr.dout_ref <= mem[rd_addr];
					intr.tx_valid_ref <=1;
				end
			endcase
		end
	end

endmodule