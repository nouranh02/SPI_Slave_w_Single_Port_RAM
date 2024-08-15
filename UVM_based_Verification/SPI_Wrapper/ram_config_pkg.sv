package ram_config_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

	class ram_config extends uvm_object;
		`uvm_object_utils(ram_config)
		
		virtual ram_if ram_vif;
		virtual ram_ref_if ram_ref_vif;
		uvm_active_passive_enum active;

		function new(string name = "ram_config");
			super.new(name);
		endfunction : new
		
	endclass : ram_config
	
endpackage : ram_config_pkg