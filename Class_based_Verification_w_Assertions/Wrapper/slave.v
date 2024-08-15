module slave(MOSI,SS_n,clk,rst_n,tx_valid,tx_data,rx_data,rx_valid,MISO);

	//Parameterized Design -> data width is a function of ADDR_SIZE
	parameter ADDR_SIZE = 8;

	input MOSI,SS_n,clk,rst_n,tx_valid;
	input [ADDR_SIZE-1:0] tx_data;			//param
	output [ADDR_SIZE+1:0] rx_data;		//param
	output reg rx_valid;
	output reg MISO;

	parameter IDLE = 3'b000;
	parameter READ_DATA = 3'b001;
	parameter READ_ADD = 3'b010;
	parameter CHK_CMD = 3'b011;
	parameter WRITE = 3'b100;
	parameter WAIT_WR = 3'b101;
	parameter WAIT_RD = 3'b110;
	parameter WAIT_RD2 = 3'b111;
	reg [2:0] cs,ns;
	reg start_to_give,start_to_take;
	reg [ADDR_SIZE-1:0] temp;				//param
	reg rd_addr_received;
	reg [3:0] i = 0 ;
	reg [3:0] j = 0;
	//reg [4:0] k = 0;

	reg [ADDR_SIZE:0] rx_temp;


/////////////////////////////////Original Code//////////////////////////////////////
/*

	always@(posedge clk or negedge rst_n)	begin
		if(~rst_n)	begin
			cs <= IDLE ;
		end
		else	begin
			cs <= ns ;
		end
	end
	//Next state logic
	always@(cs,SS_n,MOSI)	begin
		case(cs)
			IDLE:
				if(SS_n)		begin
					ns <= IDLE ;
				end
				else	begin
					ns <= CHK_CMD ;
				end
			READ_DATA:
				if(~SS_n &&( start_to_take || start_to_give ))	begin
					ns <= READ_DATA ;
				end
				else	begin
					ns <= IDLE ;
				end
			READ_ADD:
				if(~SS_n && start_to_give)	begin
					ns <= READ_ADD ;
				end
				else	begin
					ns <= IDLE ;
				end
			CHK_CMD:
				if( (~SS_n) && (MOSI == 1) && rd_addr_received )	begin
					ns <= READ_DATA ;
				end
				else if( (~SS_n) && (MOSI == 1) )	begin
					ns <= READ_ADD ;
				end
				else if ( (~SS_n) && (MOSI == 0) )	begin
					ns <= WRITE ;
				end
				else if (SS_n)	begin
					ns <= IDLE ;
				end
			WRITE:
				if(~SS_n && start_to_give)	begin
					ns <= WRITE ;
				end
				else	begin
					ns <= IDLE ;
				end

			default: ns <= IDLE;
		endcase
	end

	always @(posedge clk) begin
		if (cs == READ_ADD)
			rd_addr_received=1;
		else if (cs == READ_DATA)
			rd_addr_received=0;
	end

	always@(posedge clk)	begin
		if (start_to_give ==1 && ~SS_n)	begin
			rx_data <= {rx_data[ADDR_SIZE:0],MOSI};		//param
			if (i==ADDR_SIZE+1) begin 					//param
				i<=0;
				rx_valid =1;
				start_to_give <= 0;
			end
			else  begin
				i <= i + 1 ;
				rx_valid <= 0;
			end
		end
		else begin
			rx_valid <=0;
			if((cs == CHK_CMD) && (SS_n == 0))	
				start_to_give <= 1;
		end
	end

	

	always@ (posedge tx_valid)begin
		start_to_take <=1;
		temp <= tx_data;
	end

	always@(start_to_take,posedge clk)	begin
		if (start_to_take==1 && ~SS_n) begin
			MISO <= temp[0];
			temp <= {1'b0,temp[ADDR_SIZE-1:1]};			//param
			if (j == ADDR_SIZE-1)	begin 				//param
				start_to_take <= 0 ;
				j <= 0;
			end
			else begin
			j <= j + 1 ;
			end
		end
	end
*/
////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////Edited Code////////////////////////////////////////

	always@(posedge clk or negedge rst_n)	begin
		if(~rst_n)	begin
			cs <= IDLE ;
		end
		else	begin
			cs <= ns ;
		end
	end
	//Next state logic
	always@(cs,SS_n,MOSI)	begin
		case(cs)
			IDLE:
				if(SS_n)		begin
					ns <= IDLE ;
				end
				else	begin
					ns <= CHK_CMD ;
				end
			READ_DATA:
				if(SS_n) 	begin
					ns <= IDLE;
				end
				else if( start_to_take )	begin
					ns <= READ_DATA ;
				end
			READ_ADD:
				if(~SS_n && start_to_give)	begin
					ns <= READ_ADD ;
				end
				else if(SS_n)	begin
					ns <= IDLE ;
				end
			CHK_CMD:
				if(SS_n) ns <= IDLE;
				else begin
					if(MOSI) ns <= WAIT_RD;
					else ns <= WAIT_WR;
				end
			WAIT_WR:
				if(SS_n || MOSI) ns <= IDLE;
				else ns <= WRITE;
			WAIT_RD:
				if(SS_n || ~MOSI) ns <= IDLE;
				else ns <= WAIT_RD2;
			WAIT_RD2:
				if(SS_n) ns <= IDLE;
				else begin
					if(rd_addr_received && MOSI) ns <= READ_DATA;
					else if(~rd_addr_received && ~MOSI) ns <= READ_ADD;
					else ns <= IDLE;
				end
			WRITE:
				if(~SS_n && start_to_give)	begin
					ns <= WRITE ;
				end
				else if(SS_n)	begin
					ns <= IDLE ;
				end

			default: ns <= IDLE;
		endcase
	end

	always @(posedge clk or negedge rst_n) begin
		if(cs == IDLE) begin
			rx_temp <= 0;
			rx_valid <= 0;
			MISO <= 0;
			start_to_give <= 0;
			start_to_take <= 0;
			temp <= 0;
		end
	end

	always @(posedge clk) begin
		if (cs == READ_ADD)
			rd_addr_received=1;
		else if (cs == READ_DATA)
			rd_addr_received=0;
	end

	always@(posedge clk or negedge rst_n) begin
		if(~rst_n || SS_n) begin
			rx_temp <= 0;
			rx_valid <= 0;
			i <= 0;
		end
		else begin
			if (start_to_give)	begin
				rx_temp <= {rx_temp[ADDR_SIZE-1:0],MOSI};	//param
				if (i==ADDR_SIZE) begin 					//param
					i<=0;
					start_to_give <= 0;
					rx_valid <= 1;
				end
				else  begin
					i <= i + 1 ;
					rx_valid <= 0;
				end
			end
			else begin
				rx_valid <= 0;
				if( ((cs == WAIT_WR) && ~MOSI) || ((cs == WAIT_RD) && MOSI) ) begin
					start_to_give <= 1;
					i <= 0;
				end
			end
		end
	end
/*
	always @(posedge clk or negedge rst_n) begin
		if(~rst_n || SS_n) k <= 0;
		else begin
			if(cs == READ_DATA) k <= k + 1;
			else k <= 0;
		end
	end
*/
	always@ (posedge tx_valid or negedge rst_n)begin
		if(~rst_n) begin
			temp <= 0;
			start_to_take <=0;
			rd_addr_received <= 0;
		end
		else if(cs == READ_DATA) begin
			start_to_take <=1;
			temp <= tx_data;
		end
		else start_to_take <= 0;
	end

	always@(posedge clk or negedge rst_n)	begin
		if(~rst_n || SS_n) begin
			MISO <= 0;
			start_to_take <= 0;
			j <= 0;
		end
		else begin
			if (tx_valid && start_to_take) begin
				MISO <= temp[ADDR_SIZE-1];
				temp <= {temp[ADDR_SIZE-2:0], 1'b0};	//param
				if (j == ADDR_SIZE)	begin 				//param
					start_to_take <= 0 ;
					j <= 0;
				end
				else begin
					j <= j + 1 ;
				end
			end
			else begin
				MISO <= 0;
				start_to_take <= 0;
				j <= 0;
			end
		end
	end


	assign rx_data = ( (cs == READ_ADD) || (cs == READ_DATA) ) ? {1'b1, rx_temp} : {1'b0, rx_temp};

////////////////////////////////////////////////////////////////////////////////////


endmodule