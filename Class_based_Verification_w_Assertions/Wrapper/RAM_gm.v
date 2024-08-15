module RAM_gm (clk, rst_n, din, rx_valid, dout, tx_valid);
	parameter MEM_DEPTH = 256;
	parameter ADDR_SIZE = 8;

	input [9:0] din;
	input clk, rst_n , rx_valid;
	output reg [7:0] dout;
	output reg tx_valid;

	reg [ADDR_SIZE-1:0] wr_addr, rd_addr;
	reg [ADDR_SIZE-1:0] mem [MEM_DEPTH-1:0];

	wire [1:0] signal;
	wire [ADDR_SIZE-1:0] data;

	assign signal = din[ADDR_SIZE+1:ADDR_SIZE];
    assign data = din[ADDR_SIZE-1:0];

	always @(posedge clk or negedge rst_n) begin
		if(~rst_n) begin
			dout <= 0;
			tx_valid <= 0;
			wr_addr <= 0;
			rd_addr <= 0;
		end
		else if(rx_valid) begin
			case (signal)
				2'b00: begin
					wr_addr <= data;
					tx_valid <=0;
				end
				2'b01: begin
					mem [wr_addr] <= data;
					tx_valid <=0;
				end	
				2'b10: begin
					rd_addr <= data;
					tx_valid <=0;
				end
				default: begin
					dout <= mem[rd_addr];
					tx_valid <=1;
				end
			endcase
		end
	end

endmodule