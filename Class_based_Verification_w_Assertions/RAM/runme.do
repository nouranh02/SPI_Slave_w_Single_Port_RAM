vlog ram.sv RAM_pkg.sv RAM_tb.sv RAM_sva.sv +cover
vsim -voptargs=+acc work.RAM_tb -sv_seed random -cover

add wave -position insertpoint  \
sim:/RAM_tb/clk \
sim:/RAM_tb/rst_n \
sim:/RAM_tb/rx_valid \
sim:/RAM_tb/din \
sim:/RAM_tb/signal \
sim:/RAM_tb/data \
sim:/RAM_tb/DUT/write_addr \
sim:/RAM_tb/DUT/read_addr \
sim:/RAM_tb/tx_valid \
sim:/RAM_tb/tx_valid_exp \
sim:/RAM_tb/dout \
sim:/RAM_tb/dout_exp \
sim:/RAM_tb/DUT/mem

add wave -position insertpoint  \
sim:/RAM_tb/correct_count \
sim:/RAM_tb/error_count


add wave /RAM_tb/DUT/ram_sva_inst/assertion_reset /RAM_tb/DUT/ram_sva_inst/assertion_rx_inv /RAM_tb/DUT/ram_sva_inst/assertion_save_wr /RAM_tb/DUT/ram_sva_inst/assertion_wr_d /RAM_tb/DUT/ram_sva_inst/assertion_save_rd /RAM_tb/DUT/ram_sva_inst/assertion_rd_d /RAM_tb/DUT/ram_sva_inst/assertion_tx_a /RAM_tb/DUT/ram_sva_inst/assertion_tx_in /RAM_tb/DUT/ram_sva_inst/assertion_wr_op /RAM_tb/DUT/ram_sva_inst/assertion_rd_op /RAM_tb/DUT/ram_sva_inst/assertion_main

coverage save RAM_tb.ucdb -onexit

run -all