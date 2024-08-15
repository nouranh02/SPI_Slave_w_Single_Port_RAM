package SPI_Wrapper_env_pkg;
import SPI_Wrapper_agent_pkg::*;
import SPI_Wrapper_scoreboard_pkg::*;
import SPI_Wrapper_coverage_pkg::*;
import shared_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
	
	class SPI_Wrapper_env extends uvm_env;
		`uvm_component_utils(SPI_Wrapper_env)

		SPI_Wrapper_agent agt;
		SPI_Wrapper_scoreboard sb;
		SPI_Wrapper_coverage cov;

		function new(string name = "SPI_Wrapper_env", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			agt = SPI_Wrapper_agent::type_id::create("agt", this);
			sb = SPI_Wrapper_scoreboard::type_id::create("sb", this);
			cov = SPI_Wrapper_coverage::type_id::create("cov", this);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			agt.agt_ap.connect(sb.sb_export);
			agt.agt_ap.connect(cov.cov_export);
		endfunction : connect_phase

	endclass : SPI_Wrapper_env

endpackage : SPI_Wrapper_env_pkg