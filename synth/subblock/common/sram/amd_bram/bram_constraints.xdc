create_clock -name clock -period 4 -waveform {0 2} [get_ports i_wclk]
create_clock -name clock -period 4 -waveform {0 2} [get_ports i_rclk]
