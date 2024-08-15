module RAM(clk, rst_n, rx_valid, din, tx_valid, dout);
	parameter MEM_DEPTH = 256;
	parameter ADDR_SIZE = 8;

	input clk, rst_n, rx_valid;
	input [ADDR_SIZE+1:0] din;

	output reg tx_valid;
	output reg [ADDR_SIZE-1:0] dout;
	wire [ADDR_SIZE-1:0] data;
	wire [1:0] signal;

	reg [ADDR_SIZE-1:0] mem [MEM_DEPTH-1:0];
	reg [ADDR_SIZE-1:0] wr_addr, rd_addr;

    assign signal = din[ADDR_SIZE+1:ADDR_SIZE];
    assign data = din[ADDR_SIZE-1:0];
	always @(posedge clk) begin
		if(~rst_n) begin
			tx_valid <= 0;
			dout <= 0;
			wr_addr <= 0;
			rd_addr <= 0;
		end
		else begin
			case(signal)
			2'b00: begin
				if(rx_valid) wr_addr <= data;
				tx_valid <= 0;
			end
			2'b01: begin
				if(rx_valid) mem[wr_addr] <= data;
				tx_valid <= 0;
			end
			2'b10: begin
				if(rx_valid) rd_addr <= data;
				tx_valid <= 0;
			end
			2'b11: begin
				dout <= mem[rd_addr];
				tx_valid <= 1;
			end
			endcase
		end
	end
endmodule