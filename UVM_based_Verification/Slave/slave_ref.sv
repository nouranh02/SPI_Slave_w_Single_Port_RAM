module slave_ref(slave_ref_if.DUT intr);

	parameter IDLE = 3'b000;
	parameter CHK_CMD = 3'b001;
	parameter WRITE = 3'b010;
	parameter READ_ADD = 3'b011;
	parameter READ_DATA = 3'b100;
	parameter WAIT_WR = 3'b101;
	parameter WAIT_RD = 3'b110;
	parameter WAIT_RD2 = 3'b111;

    (* fsm_encoding = "gray" *)
	reg [2:0] cs, ns;
	reg data_addr; //0: addr, 1: data
	reg [4:0] bit_cntr_wr, bit_cntr_rd; //counting cycles - indicates end of state

	reg f_wr, f_rd, f_rd_d;

	reg [intr.ADDR_SIZE:0] temp_wr;
	reg [intr.ADDR_SIZE-1:0] temp_rd, temp_tx;

	reg f_tx;

	//State Memory
	always @(posedge intr.clk or negedge intr.rst_n) begin
		if(~intr.rst_n) cs <= IDLE;
		else cs <= ns;
	end

	//Next State Logic
	always @(*) begin
		case(cs)
		IDLE: ns = (intr.SS_n) ? IDLE : CHK_CMD;
		CHK_CMD: begin
			if(intr.SS_n) ns = IDLE;
			else begin
				if(intr.MOSI) ns = WAIT_RD;
				else ns = WAIT_WR;
			end
		end
		WAIT_WR: ns = (intr.SS_n) ? IDLE : (intr.MOSI) ? IDLE : WRITE;
		WAIT_RD: begin
			if(intr.SS_n) ns = IDLE;
			else begin
				if(~intr.MOSI) ns = IDLE;
				else ns = WAIT_RD2;
			end
		end
		WAIT_RD2: begin
			if(intr.SS_n) ns = IDLE;
			else begin
				if(intr.MOSI && data_addr) ns = READ_DATA;
				else if(~intr.MOSI && ~data_addr) ns = READ_ADD;
				else ns = IDLE;
			end
		end
		WRITE: ns = (intr.SS_n) ? IDLE : WRITE;
		READ_ADD: ns = (intr.SS_n) ? IDLE : READ_ADD;
		READ_DATA: ns = (intr.SS_n) ? IDLE : READ_DATA;
		default: ns = IDLE;
		endcase
	end

	//Output Logic
	always @(posedge intr.tx_valid or negedge intr.rst_n) begin
		if(~intr.rst_n) temp_tx <= 0;
		else if(cs == READ_DATA) temp_tx <= intr.tx_data;
	end

	always @(posedge intr.clk or negedge intr.rst_n) begin
		if(~intr.rst_n) begin
			intr.MISO_ref <= 0;
			intr.rx_valid_ref <= 0;
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
				intr.MISO_ref <= 0;
				intr.rx_valid_ref <= 0;
				temp_wr <= 0;
				temp_rd <= 0;
				bit_cntr_wr <= 0;
				bit_cntr_rd <= 0;
				f_wr <= 1;
				f_rd <= 1;
				f_rd_d <= 1;
			end
			WRITE: begin
				temp_wr <= {temp_wr[intr.ADDR_SIZE-1:0], intr.MOSI}; //Shift OP (Serial to Parallel)
				bit_cntr_wr <= bit_cntr_wr + 1;
				if(f_wr && (bit_cntr_wr == (intr.ADDR_SIZE))) begin //next bit_cntr=10, intr.rx_data_ref is ready
					intr.rx_valid_ref <= 1;
					bit_cntr_wr <= 0;
					f_wr <= 0;
				end
				else intr.rx_valid_ref <= 0; //intr.rx_data_ref is not ready yet
			end
			READ_ADD: begin
				temp_rd <= {temp_rd[intr.ADDR_SIZE-2:0], intr.MOSI}; //Shift OP (Serial to Parallel)
				bit_cntr_wr <= bit_cntr_wr + 1;
				if(f_rd && (bit_cntr_wr == (intr.ADDR_SIZE-1))) begin //next bit_cntr=10, intr.rx_data_ref is ready
					intr.rx_valid_ref <= 1;
					bit_cntr_wr <= 0;
					f_rd <= 0;
				end
				else intr.rx_valid_ref <= 0; //intr.rx_data_ref is not ready yet
				if(intr.SS_n) data_addr <= 1; //intr.SS_n high -> end of state -> READ_DATA next
			end
			READ_DATA: begin
				if(f_rd && (bit_cntr_wr < intr.ADDR_SIZE)) begin //bit_cntr<10, intr.rx_data_ref (dummy) is being transferred
					temp_rd <= {temp_rd[intr.ADDR_SIZE-2:0], intr.MOSI}; //Shift OP (Serial to Parallel)
					if(bit_cntr_wr == (intr.ADDR_SIZE-1)) begin //next bit_cntr=10, intr.rx_data_ref is ready
						if(intr.tx_valid) intr.rx_valid_ref <= 0;
						else intr.rx_valid_ref <= 1;
						f_rd <= 0;
					end
					bit_cntr_wr <= bit_cntr_wr + 1;
				end
				else begin
					bit_cntr_wr <= 0;
					intr.rx_valid_ref <= 0;
				end
				if(f_tx && f_rd_d && intr.tx_valid) begin
					intr.MISO_ref <= temp_tx[intr.ADDR_SIZE-1-bit_cntr_rd]; //Parallel to Serial
					if(bit_cntr_rd == (intr.ADDR_SIZE-2)) bit_cntr_rd <= 0; //bit_cntr_rd range=0:7
					if(bit_cntr_rd > (intr.ADDR_SIZE-1)) begin //next bit_cntr=8, intr.tx_data is ready
						intr.MISO_ref <= 0;
						f_rd_d <= 0;
						f_tx <= 0;
					end
					bit_cntr_rd <= bit_cntr_rd + 1;
				end
				else begin
					intr.MISO_ref <= 0; //intr.MISO_ref=0 as long as intr.tx_valid is low
					bit_cntr_rd <= 0;
				end
				if(intr.SS_n) data_addr <= 0; //intr.SS_n high -> end of state -> READ_ADD next
			end
			default: begin
				intr.MISO_ref <= 0;
				intr.rx_valid_ref <= 0;
				temp_wr <= 0;
				temp_rd <= 0;
				bit_cntr_wr <= 0;
				bit_cntr_rd <= 0;
				f_tx <= 0;
			end
			endcase

			if(intr.SS_n) begin
				temp_wr <= 0;
				temp_rd <= 0;
				intr.rx_valid_ref <= 0;
				intr.MISO_ref <= 0;
				f_tx <= 0;
			end
		end
	end

	assign intr.rx_data_ref = (cs == READ_DATA) ? {2'b11, temp_rd} : (cs == READ_ADD) ? {2'b10, temp_rd} : {1'b0, temp_wr};

	always @(posedge intr.tx_valid or negedge intr.rst_n) begin
		if(~intr.rst_n || intr.SS_n) f_tx <= 0;
		else f_tx <= 1;
	end
endmodule