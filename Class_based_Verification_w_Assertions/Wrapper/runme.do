vlog SPI_Wrapper.sv slave.v ram.sv MASTER_SPI_gm.v RAM_gm.v SPI_SLAVE_gm.v wrapper_pkg.sv wrapper_sva.sv SPI_Wrapper_tb.sv +cover
vsim -voptargs=+acc work.SPI_Wrapper_tb -sv_seed 2455693777 -classdebug -cover

add wave -position insertpoint  \
sim:/SPI_Wrapper_tb/clk \
sim:/SPI_Wrapper_tb/rst_n \
sim:/SPI_Wrapper_tb/SS_n \
sim:/SPI_Wrapper_tb/MOSI \
sim:/SPI_Wrapper_tb/MISO \
sim:/SPI_Wrapper_tb/MISO_exp \
sim:/SPI_Wrapper_tb/temp_address \
sim:/SPI_Wrapper_tb/saved_MISO \

add wave -position insertpoint  \
sim:/SPI_Wrapper_tb/DUT/tx_data1 \
sim:/SPI_Wrapper_tb/GM/tx_data \
sim:/SPI_Wrapper_tb/DUT/tx_valid1 \
sim:/SPI_Wrapper_tb/GM/tx_valid \
sim:/SPI_Wrapper_tb/DUT/rx_valid1 \
sim:/SPI_Wrapper_tb/GM/rx_valid \
sim:/SPI_Wrapper_tb/DUT/rx_data1 \
sim:/SPI_Wrapper_tb/GM/rx_data \


add wave -position insertpoint  \
sim:/SPI_Wrapper_tb/DUT/r1/write_addr \
sim:/SPI_Wrapper_tb/GM/RAM1/wr_addr \
sim:/SPI_Wrapper_tb/DUT/r1/read_addr \
sim:/SPI_Wrapper_tb/GM/RAM1/rd_addr \
sim:/SPI_Wrapper_tb/DUT/r1/mem \
sim:/SPI_Wrapper_tb/GM/RAM1/mem \

add wave -position insertpoint  \
sim:/SPI_Wrapper_tb/correct_count \
sim:/SPI_Wrapper_tb/error_count

add wave /SPI_Wrapper_tb/DUT/wrap_sva_inst/assertion_reset_asserted /SPI_Wrapper_tb/DUT/wrap_sva_inst/assertion_no_wr_op /SPI_Wrapper_tb/DUT/wrap_sva_inst/assertion_SS_inactive /SPI_Wrapper_tb/DUT/wrap_sva_inst/assertion_MISO_no_rd /SPI_Wrapper_tb/DUT/wrap_sva_inst/assertion_MISO_tx_inactive

coverage save SPI_Wrapper_tb.ucdb -onexit

run -all