module MASTER_SPI_tb();
	parameter ADDR_SIZE = 8;
	reg clk, rst_n, SS_n, MOSI;
	wire MISO;

	MASTER_SPI #(.ADDR_SIZE(ADDR_SIZE)) MASTER_SPI1(clk, rst_n, SS_n, MOSI, MISO);

	initial begin
		clk = 0;
		forever #1 clk = ~clk;
	end

	initial begin
		$readmemh("RAM.dat", MASTER_SPI1.RAM1.mem);
		rst_n = 0; SS_n = 1; MOSI = 0;
		repeat (20) @(negedge clk);
		
		rst_n = 1;
		@(negedge clk);
		repeat(20) begin
			SS_n = 0;
			@(negedge clk);
			MOSI = 0;
			@(negedge clk);
			MOSI = 0;
			@(negedge clk);
			MOSI = 0;
			@(negedge clk);
			repeat(ADDR_SIZE) begin
				MOSI = $random;
				@(negedge clk);
			end
			SS_n = 1;
			@(negedge clk);
			//////////////////////
			//////////////////////
			SS_n = 0;
			@(negedge clk);
			MOSI = 0;
			@(negedge clk);
			MOSI = 0;
			@(negedge clk);
			MOSI = 1;
			@(negedge clk);
			repeat(ADDR_SIZE) begin
				MOSI = $random;
				@(negedge clk);
			end
			SS_n = 1;
			@(negedge clk);
			//////////////////////
			//////////////////////
			SS_n = 0;
			@(negedge clk);
			MOSI = 1;
			@(negedge clk);
			MOSI = 1;
			@(negedge clk);
			MOSI = 0;
			@(negedge clk);
			repeat(ADDR_SIZE) begin
				MOSI = $random;
				@(negedge clk);
			end
			SS_n = 1;
			@(negedge clk);
			//////////////////////
			//////////////////////
			SS_n = 0;
			@(negedge clk);
			MOSI = 1;
			@(negedge clk);
			MOSI = 1;
			@(negedge clk);
			MOSI = 1;
			@(negedge clk);
			repeat(ADDR_SIZE) begin
				MOSI = $random;
				@(negedge clk);
			end
			MOSI = 0;
			repeat(ADDR_SIZE+1) @(negedge clk);
			SS_n = 1;
			@(negedge clk);
			//////////////////////
			//////////////////////
		end
		$stop;
	end
endmodule