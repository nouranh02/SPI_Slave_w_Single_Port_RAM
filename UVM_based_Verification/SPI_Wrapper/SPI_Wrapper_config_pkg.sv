package SPI_Wrapper_config_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

	class SPI_Wrapper_config extends uvm_object;
		`uvm_object_utils(SPI_Wrapper_config)
		
		virtual SPI_Wrapper_if SPI_Wrapper_vif;
		virtual SPI_Wrapper_ref_if SPI_Wrapper_ref_vif;
		uvm_active_passive_enum active;

		function new(string name = "SPI_Wrapper_config");
			super.new(name);
		endfunction : new
		
	endclass : SPI_Wrapper_config
	
endpackage : SPI_Wrapper_config_pkg