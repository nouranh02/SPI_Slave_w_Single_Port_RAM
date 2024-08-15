import slave_test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module slave_top;
	bit clk;

	initial begin
		forever #1 clk = ~clk;
	end

	slave_if slaveif (clk);
	slave DUT (slaveif);

	slave_ref_if slaverefif (clk);
	slave_ref REF (slaverefif);

	initial begin
		uvm_config_db#(virtual slave_if)::set(null, "uvm_test_top", "SLAVE_IF", slaveif);
		uvm_config_db#(virtual slave_ref_if)::set(null, "uvm_test_top", "SLAVE_REF_IF", slaverefif);
		run_test("slave_test");
	end

endmodule : slave_top