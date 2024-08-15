module SPI_SLAVE_gm(clk, rst_n, SS_n, MOSI, MISO, rx_data, rx_valid, tx_data, tx_valid);
	parameter ADDR_SIZE = 8;

	parameter IDLE = 3'b000;
	parameter CHK_CMD = 3'b001;
	parameter WRITE = 3'b010;
	parameter READ_ADD = 3'b011;
	parameter READ_DATA = 3'b100;
	parameter WAIT_WR = 3'b101;
	parameter WAIT_RD = 3'b110;
	parameter WAIT_RD2 = 3'b111;

	input clk, rst_n, SS_n, MOSI, tx_valid;
	input [ADDR_SIZE-1:0] tx_data;

	output reg MISO, rx_valid;
	output [ADDR_SIZE+1:0] rx_data;

    (* fsm_encoding = "gray" *)
	reg [2:0] cs, ns;
	reg data_addr; //0: addr, 1: data
	reg [4:0] bit_cntr_wr, bit_cntr_rd; //counting cycles - indicates end of state

	reg f_wr, f_rd, f_rd_d;

	reg [ADDR_SIZE:0] temp_wr;
	reg [ADDR_SIZE-1:0] temp_rd;

	reg f_tx;

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
				if(MOSI) ns = WAIT_RD;
				else ns = WAIT_WR;
			end
		end
		WAIT_WR: ns = (SS_n) ? IDLE : (MOSI) ? IDLE : WRITE;
		WAIT_RD: begin
			if(SS_n) ns = IDLE;
			else begin
				if(~MOSI) ns = IDLE;
				else ns = WAIT_RD2;
			end
		end
		WAIT_RD2: begin
			if(SS_n) ns = IDLE;
			else begin
				if(MOSI && data_addr) ns = READ_DATA;
				else if(~MOSI && ~data_addr) ns = READ_ADD;
				else ns = IDLE;
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
			temp_wr <= 0;
			temp_rd <= 0;
			bit_cntr_wr <= 0;
			bit_cntr_rd <= 0;
			data_addr <= 0;
			f_wr <= 1;
			f_rd <= 1;
			f_rd_d <= 1;
		end
		else begin
			case(cs)
			IDLE: begin
				MISO <= 0;
				rx_valid <= 0;
				temp_wr <= 0;
				temp_rd <= 0;
				bit_cntr_wr <= 0;
				bit_cntr_rd <= 0;
				f_wr <= 1;
				f_rd <= 1;
				f_rd_d <= 1;
			end
			WRITE: begin
				temp_wr <= {temp_wr[ADDR_SIZE-1:0], MOSI}; //Shift OP (Serial to Parallel)
				bit_cntr_wr <= bit_cntr_wr + 1;
				if(f_wr && (bit_cntr_wr == (ADDR_SIZE))) begin //next bit_cntr=10, rx_data is ready
					rx_valid <= 1;
					bit_cntr_wr <= 0;
					f_wr <= 0;
				end
				else rx_valid <= 0; //rx_data is not ready yet
			end
			READ_ADD: begin
				temp_rd <= {temp_rd[ADDR_SIZE-2:0], MOSI}; //Shift OP (Serial to Parallel)
				bit_cntr_wr <= bit_cntr_wr + 1;
				if(f_rd && (bit_cntr_wr == (ADDR_SIZE-1))) begin //next bit_cntr=10, rx_data is ready
					rx_valid <= 1;
					bit_cntr_wr <= 0;
					f_rd <= 0;
				end
				else rx_valid <= 0; //rx_data is not ready yet
				if(SS_n) data_addr <= 1; //SS_n high -> end of state -> READ_DATA next
			end
			READ_DATA: begin
				if(f_rd && (bit_cntr_wr < ADDR_SIZE)) begin //bit_cntr<10, rx_data (dummy) is being transferred
					temp_rd <= {temp_rd[ADDR_SIZE-2:0], MOSI}; //Shift OP (Serial to Parallel)
					if(bit_cntr_wr == (ADDR_SIZE-1)) begin //next bit_cntr=10, rx_data is ready
						if(tx_valid) rx_valid <= 0;
						else rx_valid <= 1;
						f_rd <= 0;
					end
					bit_cntr_wr <= bit_cntr_wr + 1;
				end
				else begin
					bit_cntr_wr <= 0;
					rx_valid <= 0;
					if(f_tx && f_rd_d && tx_valid) begin
						MISO <= tx_data[ADDR_SIZE-1-bit_cntr_rd]; //Parallel to Serial
						if(bit_cntr_rd == (ADDR_SIZE-2)) bit_cntr_rd <= 0; //bit_cntr_rd range=0:7
						if(bit_cntr_rd > (ADDR_SIZE-1)) begin //next bit_cntr=8, tx_data is ready
							MISO <= 0;
							f_rd_d <= 0;
							f_tx <= 0;
						end
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
				temp_wr <= 0;
				temp_rd <= 0;
				bit_cntr_wr <= 0;
				bit_cntr_rd <= 0;
				f_tx <= 0;
			end
			endcase

			if(SS_n) begin
				temp_wr <= 0;
				temp_rd <= 0;
				rx_valid <= 0;
				MISO <= 0;
				f_tx <= 0;
			end
		end
	end

	assign rx_data = (cs == READ_DATA) ? {2'b11, temp_rd} : (cs == READ_ADD) ? {2'b10, temp_rd} : {1'b0, temp_wr};

	always @(posedge tx_valid or negedge rst_n) begin
		if(~rst_n || SS_n) f_tx <= 0;
		else f_tx <= 1;
	end
endmodule