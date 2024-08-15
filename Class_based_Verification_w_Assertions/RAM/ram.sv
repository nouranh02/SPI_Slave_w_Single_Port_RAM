module ram (din,clk,rst_n,rx_valid,dout,tx_valid);
	parameter MEM_DEPTH = 256;
	parameter ADDR_SIZE = 8;

	input [9:0] din;
	input clk, rst_n , rx_valid;
	output reg [7:0] dout;
	output reg tx_valid;


	//Internal Signals are to be passed to Assertions -> Whitebox Verification
	//Datatype converted from (reg) to (logic)
	logic [ADDR_SIZE-1:0] write_addr, read_addr;
	logic [ADDR_SIZE-1:0] mem [MEM_DEPTH-1:0];



/////////////////////////////////Original Code//////////////////////////////////

/*	
	integer i=0;
	always @(posedge clk,negedge rst_n) begin
		if(~rst_n) begin
			for (i=0; i < MEM_DEPTH; i=i+1) begin 		//memory values should not equal zero following each reset, only Module outputs (and wr/rd addresses).
				mem[i] = 0;
			end
		end
		else if(rx_valid) begin
			case (din[9:8])								//Should use parameter (ADDR_SIZE) instead of actual size
				2'b00: begin
					write_addr <= din[7:0];
					tx_valid <=0;
				end
				2'b01: begin
					mem [write_addr] <= din[7:0];
					tx_valid <=0;
				end	
				2'b10: begin
					read_addr <= din[7:0];
					tx_valid <=0;
				end
				2'b11: begin							//For Code Coverage = 100% -> This branch is moved to default
					dout <= mem[read_addr];
					tx_valid <=1;
				end
			endcase
		end
		else 
			tx_valid =0;
	end
*/
	


/////////////////////////////////Edited Code//////////////////////////////////

	always @(posedge clk,negedge rst_n) begin
		if(~rst_n) begin
			dout <= 0;
			tx_valid <= 0;
			write_addr <= 0;
			read_addr <= 0;
		end
		else if(rx_valid) begin
			case (din[ADDR_SIZE+1:ADDR_SIZE])
				2'b00: begin
					write_addr <= din[ADDR_SIZE-1:0];
					tx_valid <=0;
				end
				2'b01: begin
					mem [write_addr] <= din[ADDR_SIZE-1:0];
					tx_valid <=0;
				end	
				2'b10: begin
					read_addr <= din[ADDR_SIZE-1:0];
					tx_valid <=0;
				end
				default: begin
					dout <= mem[read_addr];
					tx_valid <=1;
				end
			endcase
		end
	end

endmodule