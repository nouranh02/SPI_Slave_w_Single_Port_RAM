package slave_config_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

	class slave_config extends uvm_object;
		`uvm_object_utils(slave_config)
		
		virtual slave_if slave_vif;
		virtual slave_ref_if slave_ref_vif;
		uvm_active_passive_enum active;

		function new(string name = "slave_config");
			super.new(name);
		endfunction : new
		
	endclass : slave_config
	
endpackage : slave_config_pkg