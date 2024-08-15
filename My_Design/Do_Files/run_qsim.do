vlib work
vlog RAM.v SPI_SLAVE.v MASTER_SPI.v MASTER_SPI_tb.v
vsim -voptargs=+acc work.MASTER_SPI_tb
add wave -position insertpoint  \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/clk \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/rst_n \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/rx_valid \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/din \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/tx_valid \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/dout \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/data \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/signal \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/mem \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/wr_addr \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/rd_addr
add wave -position insertpoint  \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/SS_n \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/MOSI \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/MISO \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/cs \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/ns \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/data_addr \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/bit_cntr_wr \
sim:/MASTER_SPI_tb/MASTER_SPI1/SPI1/bit_cntr_rd \
sim:/MASTER_SPI_tb/MASTER_SPI1/RAM1/mem
run -all