module SPI_SLAVE(clk, rst_n, SS_n, MOSI, MISO, rx_data, rx_valid, tx_data, tx_valid);
	parameter ADDR_SIZE = 8;

	parameter IDLE = 3'b000;
	parameter CHK_CMD = 3'b001;
	parameter WRITE = 3'b010;
	parameter READ_ADD = 3'b011;
	parameter READ_DATA = 3'b100;

	input clk, rst_n, SS_n, MOSI, tx_valid;
	input [ADDR_SIZE-1:0] tx_data;

	output reg MISO, rx_valid;
	output reg [ADDR_SIZE+1:0] rx_data;

    (* fsm_encoding = "gray" *)
	reg [2:0] cs, ns;
	reg data_addr; //0: addr, 1: data
	reg [4:0] bit_cntr_wr, bit_cntr_rd; //counting cycles - indicates end of state

	//State Memory
	always @(posedge clk or negedge rst_n) begin
		if(~rst_n) cs <= IDLE;
		else cs <= ns;
	end

	//Next State Logic
	always @(*) begin
		case(cs)
		IDLE: ns = (SS_n) ? IDLE : CHK_CMD;
		CHK_CMD: begin
			if(SS_n) ns = IDLE;
			else begin
				if(MOSI) begin
					if(data_addr) ns = READ_DATA; //increments on going from ADD to DATA
					else ns = READ_ADD;
				end
				else ns = WRITE;
			end
		end
		WRITE: ns = (SS_n) ? IDLE : WRITE;
		READ_ADD: ns = (SS_n) ? IDLE : READ_ADD;
		READ_DATA: ns = (SS_n) ? IDLE : READ_DATA;
		default: ns = IDLE;
		endcase
	end

	//Output Logic
	always @(posedge clk or negedge rst_n) begin
		if(~rst_n) begin
			MISO <= 0;
			rx_valid <= 0;
			rx_data <= 0;
			bit_cntr_wr <= 0;
			bit_cntr_rd <= 0;
			data_addr <= 0;
		end
		else begin
			case(cs)
			IDLE: begin
				MISO <= 0;
				rx_valid <= 0;
				rx_data <= 0;
				bit_cntr_wr <= 0;
				bit_cntr_rd <= 0;
			end
			WRITE: begin
				rx_data <= {rx_data[ADDR_SIZE:0], MOSI}; //Shift OP (Serial to Parallel)
				bit_cntr_wr <= bit_cntr_wr + 1;
				if(bit_cntr_wr == (ADDR_SIZE+1)) begin //next bit_cntr=10, rx_data is ready
					rx_valid <= 1;
					bit_cntr_wr <= 0;
				end
				else rx_valid <= 0; //rx_data is not ready yet
			end
			READ_ADD: begin
				rx_data <= {rx_data[ADDR_SIZE:0], MOSI}; //Shift OP (Serial to Parallel)
				bit_cntr_wr <= bit_cntr_wr + 1;
				if(bit_cntr_wr == (ADDR_SIZE+1)) begin //next bit_cntr=10, rx_data is ready
					rx_valid <= 1;
					bit_cntr_wr <= 0;
				end
				else rx_valid <= 0; //rx_data is not ready yet
				if(SS_n) data_addr <= 1; //SS_n high -> end of state -> READ_DATA next
			end
			READ_DATA: begin
				if(bit_cntr_wr < (ADDR_SIZE+2)) begin //bit_cntr<10, rx_data (dummy) is being transferred
					rx_data <= {rx_data[ADDR_SIZE:0], MOSI}; //Shift OP (Serial to Parallel)
					if(bit_cntr_wr == (ADDR_SIZE+1)) bit_cntr_wr <= 0; //next bit_cntr=10, rx_data is ready
					bit_cntr_wr <= bit_cntr_wr + 1;
				end
				else begin
					if(tx_valid) begin
						MISO <= tx_data[ADDR_SIZE-1-bit_cntr_rd]; //Parallel to Serial
						if(bit_cntr_rd == (ADDR_SIZE-2)) bit_cntr_rd <= 0; //bit_cntr_rd range=0:7
						if(bit_cntr_rd > (ADDR_SIZE-1)) MISO <= 0; //next bit_cntr=8, tx_data is ready
						bit_cntr_rd <= bit_cntr_rd + 1;
					end
					else begin
						MISO <= 0; //MISO=0 as long as tx_valid is low
						bit_cntr_rd <= 0;
					end
				end
				if(SS_n) data_addr <= 0; //SS_n high -> end of state -> READ_ADD next
			end
			default: begin
				MISO <= 0;
				rx_valid <= 0;
				rx_data <= 0;
				bit_cntr_wr <= 0;
				bit_cntr_rd <= 0;
				data_addr <= 0;
			end
			endcase
		end
	end
endmodule