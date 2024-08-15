import ram_test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module ram_top;
	bit clk;

	initial begin
		forever #1 clk = ~clk;
	end

	ram_if ramif (clk);
	ram DUT (ramif);

	ram_ref_if ram_refif (clk);
	ram_ref REF (ram_refif);

	initial begin
		uvm_config_db#(virtual ram_if)::set(null, "uvm_test_top", "RAM_IF", ramif);
		uvm_config_db#(virtual ram_ref_if)::set(null, "uvm_test_top", "RAM_REF_IF", ram_refif);
		run_test("ram_test");
	end

endmodule : ram_top