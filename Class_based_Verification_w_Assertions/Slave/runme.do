vlog slave_pkg.sv SPI_SLAVE.v slave.v slave_sva.sv slave_tb.sv +cover
vsim -voptargs=+acc work.slave_tb -sv_seed random -cover

add wave -position insertpoint  \
sim:/slave_tb/DUT/clk \
sim:/slave_tb/DUT/rst_n \
sim:/slave_tb/DUT/SS_n \
sim:/slave_tb/DUT/MOSI \
sim:/slave_tb/DUT/tx_valid \
sim:/slave_tb/DUT/tx_data \
sim:/slave_tb/DUT/rx_data \
sim:/slave_tb/rx_data_exp \
sim:/slave_tb/DUT/rx_valid \
sim:/slave_tb/rx_valid_exp \
sim:/slave_tb/DUT/MISO \
sim:/slave_tb/MISO_exp \
sim:/slave_tb/cs_DUT \
sim:/slave_tb/cs_gm \
sim:/slave_tb/ns_DUT \
sim:/slave_tb/ns_gm \
sim:/slave_tb/correct_count \
sim:/slave_tb/error_count

coverage save slave_tb.ucdb -onexit

add wave /slave_tb/DUT/slave_sva_inst/assertion_reset_asserted /slave_tb/DUT/slave_sva_inst/assertion_SS_inactive /slave_tb/DUT/slave_sva_inst/assertion_CHK_first /slave_tb/DUT/slave_sva_inst/assertion_CHK_WR /slave_tb/DUT/slave_sva_inst/assertion_CHK_RD /slave_tb/DUT/slave_sva_inst/assertion_MOSI_wr /slave_tb/DUT/slave_sva_inst/assertion_MOSI_rd /slave_tb/DUT/slave_sva_inst/assertion_MOSI_rd_add /slave_tb/DUT/slave_sva_inst/assertion_MOSI_rd_data /slave_tb/DUT/slave_sva_inst/assertion_no_add_add /slave_tb/DUT/slave_sva_inst/assertion_no_data_data /slave_tb/DUT/slave_sva_inst/assertion_rx /slave_tb/DUT/slave_sva_inst/assertion_rx_wr /slave_tb/DUT/slave_sva_inst/assertion_rx_rd_add /slave_tb/DUT/slave_sva_inst/assertion_rx_rd_data /slave_tb/DUT/slave_sva_inst/assertion_rx_tx /slave_tb/DUT/slave_sva_inst/assertion_rx_chk /slave_tb/DUT/slave_sva_inst/assertion_tx /slave_tb/DUT/slave_sva_inst/assertion_MISO_rd_only

run -all