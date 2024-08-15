package ram_env_pkg;
import uvm_pkg::*;
import ram_agent_pkg::*;
import ram_scoreboard_pkg::*;
import ram_coverage_pkg::*;
`include "uvm_macros.svh"

	class ram_env extends uvm_env;
		`uvm_component_utils(ram_env);

		ram_agent agt;
		ram_scoreboard sb;
		ram_coverage cov;

		function new(string name = "ram_env", uvm_component parent = null);
			super.new(name, parent);
		endfunction : new

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			agt = ram_agent::type_id::create("agt", this);
			sb = ram_scoreboard::type_id::create("sb", this);
			cov = ram_coverage::type_id::create("cov", this);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
			agt.agt_ap.connect(sb.sb_export);
			agt.agt_ap.connect(cov.cov_export);
		endfunction : connect_phase

	endclass : ram_env
endpackage : ram_env_pkg