import SPI_Wrapper_test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module SPI_Wrapper_top;
	bit clk;

	initial begin
		forever #1 clk = ~clk;
	end

	SPI_Wrapper_if SPI_Wrapperif (clk);
	SPI_Wrapper SPI_WrapperDUT (SPI_Wrapperif);

	SPI_Wrapper_ref_if SPI_Wrapper_refif (clk);
	SPI_Wrapper_ref SPI_WrapperREF (SPI_Wrapper_refif);

	slave_if slaveif (clk);
	slave slaveDUT (slaveif);

	slave_ref_if slaverefif (clk);
	slave_ref slaveREF (slaverefif);

	ram_if ramif (clk);
	ram ramDUT (ramif);

	ram_ref_if ram_refif (clk);
	ram_ref ramREF (ram_refif);

	//Design Connections
	//Slave
	assign slaveif.rst_n = SPI_Wrapperif.rst_n;
	assign slaveif.SS_n = SPI_Wrapperif.SS_n;
	assign slaveif.MOSI = SPI_Wrapperif.MOSI;
	assign slaveif.tx_valid = SPI_WrapperDUT.tx_valid1;
	assign slaveif.tx_data = SPI_WrapperDUT.tx_data1;
	assign SPI_Wrapperif.MISO = slaveif.MISO;
	assign SPI_WrapperDUT.rx_valid1 = slaveif.rx_valid;
	assign SPI_WrapperDUT.rx_data1 = slaveif.rx_data;

	//RAM
	assign ramif.rst_n = SPI_Wrapperif.rst_n;
	assign ramif.rx_valid = SPI_WrapperDUT.rx_valid1;
	assign ramif.din = SPI_WrapperDUT.rx_data1;
	assign SPI_WrapperDUT.tx_valid1 = ramif.tx_valid;
	assign SPI_WrapperDUT.tx_data1 = ramif.dout;

	//Reference Model Connections
	//Slave
	assign slaverefif.rst_n = SPI_Wrapper_refif.rst_n;
	assign slaverefif.SS_n = SPI_Wrapper_refif.SS_n;
	assign slaverefif.MOSI = SPI_Wrapper_refif.MOSI;
	assign slaverefif.tx_valid = SPI_WrapperREF.tx_valid;
	assign slaverefif.tx_data = SPI_WrapperREF.tx_data;
	assign SPI_Wrapper_refif.MISO_ref = slaverefif.MISO_ref;
	assign SPI_WrapperREF.rx_valid = slaverefif.rx_valid_ref;
	assign SPI_WrapperREF.rx_data = slaverefif.rx_data_ref;

	//RAM
	assign ram_refif.rst_n = SPI_Wrapper_refif.rst_n;
	assign ram_refif.rx_valid = SPI_WrapperREF.rx_valid;
	assign ram_refif.din = SPI_WrapperREF.rx_data;
	assign SPI_WrapperREF.tx_valid = ram_refif.tx_valid_ref;
	assign SPI_WrapperREF.tx_data = ram_refif.dout_ref;

	initial begin
		uvm_config_db#(virtual SPI_Wrapper_if)::set(null, "uvm_test_top", "SPI_Wrapper_IF", SPI_Wrapperif);
		uvm_config_db#(virtual SPI_Wrapper_ref_if)::set(null, "uvm_test_top", "SPI_Wrapper_REF_IF", SPI_Wrapper_refif);
		uvm_config_db#(virtual slave_if)::set(null, "uvm_test_top", "SLAVE_IF", slaveif);
		uvm_config_db#(virtual slave_ref_if)::set(null, "uvm_test_top", "SLAVE_REF_IF", slaverefif);
		uvm_config_db#(virtual ram_if)::set(null, "uvm_test_top", "RAM_IF", ramif);
		uvm_config_db#(virtual ram_ref_if)::set(null, "uvm_test_top", "RAM_REF_IF", ram_refif);
		run_test("SPI_Wrapper_test");
	end

endmodule : SPI_Wrapper_top