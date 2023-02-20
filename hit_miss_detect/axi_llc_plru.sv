//PLRU Module for 2-way, 4-way, 8-way, 16-way and 32-way Set-Associativity 
// Encoding bits in the register (0-> left;  1 -> right)

// Author: Gopishankar Thayyil <gthayyil@uwaterloo.ca>

// Create a SRAM for the pseudo LRU Bits
// Register Size -> (Cfg.SetAssociativity -1) * (`Cfg.NumLines)

module axi_llc_plru #(
    
    /// Static LLC configuration struct 
    parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
    /// Way indicator type
    /// EG: typedef logic [Cfg.SetAssociativity-1:0] way_ind_t;
    parameter type way_ind_t = logic,
    /// Type of the response payload expected from the tag storage
    parameter type store_res_t = logic,
    /// Datawidth for the tc sram macro (For PLRU Bit Storage)
    parameter int unsigned plru_datalen = Cfg.SetAssociativity - 1

)(
    /// Clock, positive edge triggered
    input logic   clk_i,
    /// Asynchronous reset, active low
    input logic   rst_ni,	
    /// Index bits for the PLRU SRAM Storage	
    input logic [Cfg.IndexLength-1:0] ram_index, 
    /// SPM lock signal input.
    ///
    /// For each way there is one signal. When high the way is configured as SPM. They are disabled
    /// for store requests.
    input way_ind_t spm_lock,
    /// All dirty flags as input. This indicates us if we have to write back the data.
    input  way_ind_t tag_dirty_i,
    /// req_i signal to activate miss way counter
    input logic evict_i,
    /// hit signal from the tag compare
    input logic hit_i,
    /// Bist activated (signal)
    input logic bist_i,
    /// Indicates which way the HIT Occured
    input way_ind_t   res_indicator,
    /// Way indicator for action to be performed. Is a onehot signal.
    output way_ind_t out_way_ind,
    /// Logic to lock the out_way_ind at evict box module
    output logic valid_o,
    /// Evict Flag signal
    output logic evict_o,
    /// Valid Hit after Updation
    output logic valid_o_plru,
    
    /// INPUTS/OUTPUTS FOR BIST
    /// BIST activation (from tag_store unit)
    input logic plru_gen_valid,
    /// BIST Ready for DATA 
    output logic plru_gen_ready,
    /// BIST result (reg)output (For Memory fault test) 
    output way_ind_t plru_bist_res_o,
    /// BIST End signal
    output logic plru_gen_eoc
);

`include "common_cells/registers.svh"

typedef logic [Cfg.IndexLength-1 :0] line_addr;
typedef logic [Cfg.SetAssociativity-2:0] data_plru;

//SRAM Request Signals
logic plru_request;
logic plru_we;
logic plru_bei;
logic [Cfg.IndexLength-1 :0] plru_line_addr;
logic [Cfg.SetAssociativity-2:0] plru_wdata ;
logic [Cfg.SetAssociativity-2:0] plru_rdata ;

//temp register for storage between reads and write from the SRAM
logic [Cfg.SetAssociativity-2:0] temp_ram;

//Temp register logics -- Used for temperory data storage
// in between the hit/miss update algorithms based on PLRU
logic two_temp_ram_p;
logic [2:0] four_temp_ram_p;
logic [6:0] eight_temp_ram_p;
logic [14:0] sixteen_temp_ram_p;
logic [30:0] thirtytwo_temp_ram_p;

logic two_way_temp_ram;
logic [2:0] four_way_temp_ram;
logic [6:0] eight_way_temp_ram;
logic [14:0] sixteen_way_temp_ram;
logic [30:0] thirtytwo_way_temp_ram;

logic [1:0] two_way_out_ind;
logic [3:0] four_way_out_ind;
logic [7:0] eight_way_out_ind;
logic [15:0] sixteen_way_out_ind;

// For Synchronous Write/Read from Memory
logic ram_rvalid_d, ram_rvalid_q;

// Signals for Memory BIST Operation    
logic plru_gen_req, plru_gen_we;
logic plru_bist_res_valid_i;
line_addr plru_gen_index;
data_plru plru_gen_pattern, plru_bist_pattern;
way_ind_t plru_bist_res_i;

// TC_SRAM Instantiation 
tc_sram #(
      .NumWords    ( Cfg.NumLines ),
      .DataWidth   ( plru_datalen ),
      .ByteWidth   ( plru_datalen ),
      .NumPorts    ( 32'd1        ),
      .Latency     ( 32'd0        ),
      .SimInit     ( "none"       ),
      .PrintSimCfg ( 1'b1         )
) i_plru_store (
      .clk_i   ( clk_i          ),
      .rst_ni  ( rst_ni         ),
      .req_i   ( plru_request   ),
      .we_i    ( plru_we        ),
      .addr_i  ( plru_line_addr ),
      .wdata_i ( plru_wdata     ),
      .be_i    ( plru_we        ),
      .rdata_o ( plru_rdata     )
    );
    
// Tag Pattern Generation for Memory BIST
axi_llc_tag_pattern_gen #(
    .Cfg       	( Cfg       ),
    .pattern_t 	( data_plru ),
    .way_ind_t 	( way_ind_t ),
    .index_t   	( line_addr )
  ) i_plru_pattern_gen (
    .clk_i	          ( clk_i	               ),
    .rst_ni	          ( rst_ni                 ),
    .valid_i          ( plru_gen_valid         ),
    .ready_o          ( plru_gen_ready         ),
    .index_o          ( plru_gen_index         ),
    .pattern_o        ( plru_gen_pattern       ),
    .req_o            ( plru_gen_req           ),
    .we_o             ( plru_gen_we            ),
    .bist_res_i       ( plru_bist_res_i        ),
    .bist_res_valid_i ( plru_bist_res_valid_i  ),
    .bist_res_o       ( plru_bist_res_o        ),
    .eoc_o            ( plru_gen_eoc           )
  );   
    
shift_reg #(
    .dtype ( data_plru                    ),
    .Depth ( axi_llc_pkg::TagMacroLatency )
  ) i_shift_reg_bist_plru (
    .clk_i,
    .rst_ni,
    .d_i    ( plru_gen_pattern  ),
    .d_o    ( plru_bist_pattern )
  );

// XNOR Operation (Checking) for Memory BIST
assign plru_bist_res_i = ((temp_ram) ~^ (plru_bist_pattern));
   
// Memory Read/Write delay signals    
assign ram_rvalid_d = (plru_request & ~plru_we) ? 1 : 0;    
`FFLARN(ram_rvalid_q, ram_rvalid_d, 1'b1, 1'b0, clk_i, rst_ni)
    
//--------------MEMORY READ/WRITE TASKS------------------------//

//Write task onto tc_sram (Dual port memory)
task write_tc_sram (input [Cfg.IndexLength-1 :0] ram_index, input [Cfg.SetAssociativity - 2 : 0] wdata); 

    plru_request = 1;
    plru_we = 1;
    plru_line_addr = ram_index;
    plru_wdata = wdata;
    
endtask

//Read task from tc_sram (Dual port memory)
task read_tc_sram (input [Cfg.IndexLength-1 :0] ram_index); 
		
    plru_request = 1;
    plru_we = 0;
    plru_line_addr = ram_index;

endtask

// --------------------------------------------------------------//
//-------------------------- ALL WAY HIT CHECKER TASKS----------------------------//

//Task for Two Way Hit Checking 
task two_way_hit (input [1:0] two_way_ind, output two_way_temp_ram);

    if (two_way_ind == 2'b01) begin 
        two_way_temp_ram = 1;
    end
    else if (two_way_ind == 2'b10) begin
        two_way_temp_ram = 0;
    end

endtask

//Task for Four Way Hit Checking
task four_way_hit (input [3:0] four_way_ind, input [2:0] temp_ram, output [2:0] four_way_temp_ram);

    four_way_temp_ram = temp_ram;  
    if (four_way_ind & 4'b1100) begin
        four_way_temp_ram[0] = 0;
        two_way_hit (four_way_ind[3:2], two_way_temp_ram);
        four_way_temp_ram[1] = two_way_temp_ram; 
    end
    else if (four_way_ind & 4'b0011) begin
        four_way_temp_ram[0] = 1;
        two_way_hit (four_way_ind[1:0], two_way_temp_ram);
        four_way_temp_ram[2] = two_way_temp_ram; 
    end

endtask

//Task for Eight Way Hit Checking
task eight_way_hit (input [7:0] eight_way_ind, input [6:0] temp_ram, output [6:0] eight_way_temp_ram);

    eight_way_temp_ram = temp_ram;
    if (eight_way_ind & 8'hF_0 ) begin        
        eight_way_temp_ram[0] = 0;
        four_way_hit (eight_way_ind [7:4], temp_ram [3:1], four_way_temp_ram);
        eight_way_temp_ram [3:1] = four_way_temp_ram;
    end
    else if (eight_way_ind & 8'h0_F) begin        
        eight_way_temp_ram[0] = 1;
        four_way_hit (eight_way_ind [3:0], temp_ram [6:4], four_way_temp_ram);
        eight_way_temp_ram [6:4] = four_way_temp_ram;                                
    end

endtask

//Task for Sixteen Way Hit Checking
task sixteen_way_hit (input [15:0] sixteen_way_ind, input [14:0] temp_ram, output [14:0] sixteen_way_temp_ram);

    sixteen_way_temp_ram = temp_ram;
    if (sixteen_way_ind & 16'hFF_00) begin       
        sixteen_way_temp_ram[0] = 0;
        eight_way_hit (sixteen_way_ind [15:8], temp_ram [7:1], eight_way_temp_ram);
        sixteen_way_temp_ram [7:1] = eight_way_temp_ram;
    end
    else if (sixteen_way_ind & 16'h00_FF) begin        
        sixteen_way_temp_ram[0] = 1;
        eight_way_hit (sixteen_way_ind [7:0], temp_ram [14:8], eight_way_temp_ram);
        sixteen_way_temp_ram [14:8] = eight_way_temp_ram;                                
    end

endtask

//Task for Thirtytwo Way Hit Checking
task thirtytwo_way_hit (input [31:0] thirtytwo_way_ind, input [30:0] temp_ram, output [30:0] thirtytwo_way_temp_ram);

    thirtytwo_way_temp_ram = temp_ram;
    if (thirtytwo_way_ind & 32'hFFFF_0000) begin        
        thirtytwo_way_temp_ram[0] = 0;
        sixteen_way_hit (thirtytwo_way_ind [31:16], temp_ram [15:1], sixteen_way_temp_ram);
        thirtytwo_way_temp_ram [15:1] = sixteen_way_temp_ram;
    end
    else if (thirtytwo_way_ind & 32'h0000_FFFF) begin       
        thirtytwo_way_temp_ram[0] = 1;
        sixteen_way_hit (thirtytwo_way_ind [15:0], temp_ram [30:16], sixteen_way_temp_ram);
        thirtytwo_way_temp_ram [14:8] = sixteen_way_temp_ram;                                
    end

endtask
    
// -----------------------------------------------------------------------------------------//
//-------------------------- ALL WAY MISS CHECKER TASKS----------------------------//

//Task for Two Way Miss Checking
task two_way_miss (input temp_ram, input [1:0] spm_lock, output [1:0] two_way_out_ind, output two_way_temp_ram );

    if (spm_lock == 2'b10) begin
        two_way_out_ind = 2'b01;
        two_way_temp_ram = 1;
    end                
    else if (spm_lock == 2'b01) begin
        two_way_out_ind = 2'b10;
        two_way_temp_ram = 0;
    end  
    else begin
        two_temp_ram_p = ~temp_ram;
        if (two_temp_ram_p == 0) begin
            two_way_out_ind = 2'b10;
            two_way_temp_ram = 1'b0;
        end
        else if (two_temp_ram_p == 1) begin
            two_way_out_ind = 2'b01;
            two_way_temp_ram = 1'b1;
        end
    end

endtask

//Task for Four Way Miss Checking
task four_way_miss (input [2:0] temp_ram, input [3:0] spm_lock, output [3:0] four_way_out_ind, output [2:0] four_way_temp_ram);

    begin      
        four_temp_ram_p = temp_ram;
        if (spm_lock[3:2] == 2'b11) begin
            four_temp_ram_p[0] = 1;
            four_way_temp_ram = four_temp_ram_p;
        end
        else if (spm_lock[1:0] == 2'b11) begin
            four_temp_ram_p[0] = 0;
            four_way_temp_ram = four_temp_ram_p;
        end
        else begin
            four_temp_ram_p [0] = ~temp_ram[0];
            four_way_temp_ram = four_temp_ram_p;
        end       
        if(four_temp_ram_p[0] == 0) begin
            two_way_miss (four_temp_ram_p[1], spm_lock [3:2] , two_way_out_ind, two_way_temp_ram);
            four_way_out_ind = {two_way_out_ind,2'b0};
            four_way_temp_ram [1] = two_way_temp_ram;
        end
        else if(four_temp_ram_p[0] == 1) begin
            two_way_miss (four_temp_ram_p[2], spm_lock [1:0], two_way_out_ind, two_way_temp_ram);
            four_way_out_ind = {2'b0, two_way_out_ind};
            four_way_temp_ram [2] = two_way_temp_ram;
        end                 
    end

endtask

//Task for Eight Way Miss Checking
task eight_way_miss (input [6:0] temp_ram, input [7:0] spm_lock, output [7:0] eight_way_out_ind, output [6:0] eight_way_temp_ram);

    begin     
        eight_temp_ram_p = temp_ram;
        if (spm_lock[7:4] == 4'hF) begin
            eight_temp_ram_p[0] = 1;
            eight_way_temp_ram = eight_temp_ram_p;
        end
        else if (spm_lock[3:0] == 4'hF) begin
            eight_temp_ram_p[0] = 0;
            eight_way_temp_ram = eight_temp_ram_p;
        end
        else begin
            eight_temp_ram_p [0] = ~temp_ram[0];
            eight_way_temp_ram = eight_temp_ram_p;
        end
        if(eight_temp_ram_p[0] == 0) begin
            four_way_miss (eight_temp_ram_p[3:1], spm_lock[7:4], four_way_out_ind, four_way_temp_ram);
            eight_way_out_ind = {four_way_out_ind,4'b0};
            eight_way_temp_ram [3:1] = four_way_temp_ram;
        end
        else if(eight_temp_ram_p[0] == 1) begin
            four_way_miss (eight_temp_ram_p[6:4], spm_lock[3:0], four_way_out_ind, four_way_temp_ram);
            eight_way_out_ind = {4'b0, four_way_out_ind};
            eight_way_temp_ram [6:4] = four_way_temp_ram;
        end                      
    end

endtask

//Task for Sixteen Way Miss Checking
task sixteen_way_miss (input [14:0] temp_ram, input [15:0] spm_lock, output [15:0] sixteen_way_out_ind, output [14:0] sixteen_way_temp_ram);

    begin      
        sixteen_temp_ram_p = temp_ram;
        if (spm_lock[15:8] == 8'hFF) begin
            sixteen_temp_ram_p[0] = 1;
            sixteen_way_temp_ram = sixteen_temp_ram_p;
        end
        else if (spm_lock[7:0] == 8'hFF) begin
            sixteen_temp_ram_p[0] = 0;
            sixteen_way_temp_ram = sixteen_temp_ram_p;
        end
        else begin
            sixteen_temp_ram_p [0] = ~temp_ram[0];
            sixteen_way_temp_ram = sixteen_temp_ram_p;
        end
        if(sixteen_temp_ram_p[0] == 0) begin
            eight_way_miss (sixteen_temp_ram_p[7:1], spm_lock[15:8], eight_way_out_ind, eight_way_temp_ram);
            sixteen_way_out_ind = {eight_way_out_ind,8'b0};
            sixteen_way_temp_ram [7:1] = eight_way_temp_ram;
        end
        else if(sixteen_temp_ram_p[0] == 1) begin
            eight_way_miss (sixteen_temp_ram_p[14:8], spm_lock[7:0], eight_way_out_ind, eight_way_temp_ram);
            sixteen_way_out_ind = {8'b0, eight_way_out_ind};
            sixteen_way_temp_ram [14:8] = eight_way_temp_ram;
        end                     
    end

endtask

//Task for Thirtytwo Way Miss Checking
task thirtytwo_way_miss (input [30:0] temp_ram, input [31:0] spm_lock, output [31:0] thirtytwo_way_out_ind, output [30:0] thirtytwo_way_temp_ram);

    begin      
        thirtytwo_temp_ram_p = temp_ram;
        if (spm_lock[31:16] == 16'hFFFF) begin
            thirtytwo_temp_ram_p[0] = 1;
            thirtytwo_way_temp_ram = thirtytwo_temp_ram_p;
        end
        else if (spm_lock[15:0] == 16'hFFFF) begin
            thirtytwo_temp_ram_p[0] = 0;
            thirtytwo_way_temp_ram = thirtytwo_temp_ram_p;
        end
        else begin
            thirtytwo_temp_ram_p [0] = ~temp_ram[0];
            thirtytwo_way_temp_ram = thirtytwo_temp_ram_p;
        end
        if(thirtytwo_temp_ram_p[0] == 0) begin
            sixteen_way_miss (thirtytwo_temp_ram_p[15:1], spm_lock[31:16], sixteen_way_out_ind, sixteen_way_temp_ram);
            thirtytwo_way_out_ind = {sixteen_way_out_ind,16'b0};
            thirtytwo_way_temp_ram [15:1] = sixteen_way_temp_ram;
        end
        else if(thirtytwo_temp_ram_p[0] == 1) begin
            sixteen_way_miss (thirtytwo_temp_ram_p[30:16], spm_lock[15:0], sixteen_way_out_ind, sixteen_way_temp_ram);
            thirtytwo_way_out_ind = {16'b0, sixteen_way_out_ind};
            thirtytwo_way_temp_ram [30:16] = sixteen_way_temp_ram;
        end              
    end

endtask

// -----------------------------------------------------------------------------------------------------------------------// 
   
generate
    case (Cfg.SetAssociativity)

	// 2-WAY 
        2: begin     
            always_comb begin : axi_llc_2_way  
            
            	// Outputs required for EVICTION
            	valid_o = 0; 
            	evict_o = 0;
            	out_way_ind = way_ind_t'(0);
            	// Outputs required for HIT Detection
            	valid_o_plru = 0;
            	// Temporary data storage from SRAM Unit
            	temp_ram = data_plru'(0);
          
          	    // PLRU SRAM Request Signals                	
            	plru_request = 1'b0;
    		    plru_line_addr = line_addr'(0);
    		    plru_wdata = data_plru'(0);
    		
    		    // PLRU BIST Result valid signal
    		    plru_bist_res_valid_i = 0;
    		
    		    if (bist_i) begin
                	//To initialize the SRAM to Zeros
            		plru_request    = {Cfg.SetAssociativity{plru_gen_req}};
            		plru_we         = {Cfg.SetAssociativity{plru_gen_we}};
            		plru_line_addr  = plru_gen_index;
            		plru_wdata      = plru_gen_pattern;
            		if (ram_rvalid_q) begin
            			temp_ram              = plru_rdata;
            			plru_bist_res_valid_i = 1;
            		end
            	end  

                if (hit_i && !valid_o_plru) begin 
                    //we are a hit 
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;                   
                    	two_way_hit (res_indicator, two_way_temp_ram); 
                    	write_tc_sram(ram_index,two_way_temp_ram);
                    	valid_o_plru = 1;   
                    end
                end  

                if (evict_i && !valid_o) begin              
                    //find which way to evict       
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	two_way_miss (temp_ram, spm_lock, out_way_ind, two_way_temp_ram);
                    	write_tc_sram(ram_index, two_way_temp_ram);
                    	valid_o = 1;
                    	if ((tag_dirty_i & out_way_ind) != '0)
                    		evict_o = 1'b1;
                    end	
                end

            end

        end
    


	// 4-WAY
        4: begin 

            always_comb begin : axi_llc_4_way
            
            	// Outputs required for EVICTION
            	valid_o = 0; 
            	evict_o = 0;
            	out_way_ind = way_ind_t'(0);
            	// Outputs required for HIT Detection
            	valid_o_plru = 0;
            	// Temporary data storage from SRAM Unit
            	temp_ram = data_plru'(0);
          
          	    // PLRU SRAM Request Signals                	
            	plru_request = 1'b0;
    		    plru_line_addr = line_addr'(0);
    		    plru_wdata = data_plru'(0);
    		
    		    // PLRU BIST Result valid signal
    		    plru_bist_res_valid_i = 0;
    		
    		    if (bist_i) begin
                	//To initialize the SRAM to Zeros
            		plru_request    = {Cfg.SetAssociativity{plru_gen_req}};
            		plru_we         = {Cfg.SetAssociativity{plru_gen_we}};
            		plru_line_addr  = plru_gen_index;
            		plru_wdata      = plru_gen_pattern;
            		if (ram_rvalid_q) begin
            			temp_ram              = plru_rdata;
            			plru_bist_res_valid_i = 1;
            		end
            	end

                if (hit_i && !valid_o_plru) begin
                    //we are a hit
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata; 
                    	four_way_hit (res_indicator, temp_ram, four_way_temp_ram);
                    	write_tc_sram(ram_index,four_way_temp_ram);
                    	valid_o_plru = 1;
                    end
                end
                
                if (evict_i && !valid_o) begin
                    //find which way to evict
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	four_way_miss(temp_ram, spm_lock, out_way_ind, four_way_temp_ram); 
                    	write_tc_sram(ram_index,four_way_temp_ram);   
                    	valid_o = 1;
                    	if ((tag_dirty_i & out_way_ind) != '0)
                    		evict_o = 1'b1;   
                    end              
                end  

            end

        end



	// 8-WAY
        8: begin 

            always_comb begin : axi_llc_8_way
            
            	// Outputs required for EVICTION
            	valid_o = 0; 
            	evict_o = 0;
            	out_way_ind = way_ind_t'(0);
            	// Outputs required for HIT Detection
            	valid_o_plru = 0;
            	// Temporary data storage from SRAM Unit
            	temp_ram = data_plru'(0);
          
          	    // PLRU SRAM Request Signals                	
            	plru_request = 1'b0;
    		    plru_line_addr = line_addr'(0);
    		    plru_wdata = data_plru'(0);
    		
    		    // PLRU BIST Result valid signal
    		    plru_bist_res_valid_i = 0;
    		          	
            	if (bist_i) begin
            		//To initialize the SRAM to Zeros
            		plru_request     = {Cfg.SetAssociativity{plru_gen_req}};
            		plru_we          = {Cfg.SetAssociativity{plru_gen_we}};
            		plru_line_addr   = plru_gen_index;
            		plru_wdata       = plru_gen_pattern;
            		if (ram_rvalid_q) begin
            			temp_ram              = plru_rdata;
            			plru_bist_res_valid_i = 1;
            		end
            	end
           
                if (hit_i && !valid_o_plru) begin
                    //we are a res_hit
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	eight_way_hit (res_indicator, temp_ram, eight_way_temp_ram);
                    	write_tc_sram(ram_index,eight_way_temp_ram);
                    	valid_o_plru = 1;
                	end
                  end
        
                if (evict_i && !valid_o) begin
                
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	eight_way_miss (temp_ram, spm_lock, out_way_ind, eight_way_temp_ram);
                    	write_tc_sram(ram_index,eight_way_temp_ram);
                    	valid_o = 1;
                    	if ((tag_dirty_i & out_way_ind) != '0)
                    		evict_o = 1'b1;
                    end
                end

            end

        end



	// 16-WAY
        16: begin 

            always_comb begin : axi_llc_16_way
            
            	// Outputs required for EVICTION
            	valid_o = 0; 
            	evict_o = 0;
            	out_way_ind = way_ind_t'(0);
            	// Outputs required for HIT Detection
            	valid_o_plru = 0;
            	// Temporary data storage from SRAM Unit
            	temp_ram = data_plru'(0);
          
          	    // PLRU SRAM Request Signals                	
            	plru_request = 1'b0;
    		    plru_line_addr = line_addr'(0);
    		    plru_wdata = data_plru'(0);
    		
    		    // PLRU BIST Result valid signal
    		    plru_bist_res_valid_i = 0;
    		
    		    if (bist_i) begin
                	//To initialize the SRAM to Zeros
            		plru_request   = {Cfg.SetAssociativity{plru_gen_req}};
            		plru_we        = {Cfg.SetAssociativity{plru_gen_we}};
            		plru_line_addr = plru_gen_index;
            		plru_wdata     = plru_gen_pattern;
            		if (ram_rvalid_q) begin
            			temp_ram              = plru_rdata;
            			plru_bist_res_valid_i = 1;
            		end
            	end

                if (hit_i && !valid_o_plru) begin
                    //we are a res_hit
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	sixteen_way_hit (res_indicator, temp_ram, sixteen_way_temp_ram);
                    	write_tc_sram(ram_index,sixteen_way_temp_ram);
                    	valid_o_plru = 1;
                	end
                end
                
                if (evict_i && !valid_o) begin
                    //find which way to evict
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	sixteen_way_miss (temp_ram, spm_lock, out_way_ind, sixteen_way_temp_ram);
                    	write_tc_sram(ram_index,sixteen_way_temp_ram);
                    	valid_o = 1;
                    	if ((tag_dirty_i & out_way_ind) != '0)
                    		evict_o = 1'b1;
                    end
                end

            end

        end



	// 32-WAY
        32: begin 

            always_comb begin : axi_llc_32_way
            
            	// Outputs required for EVICTION
            	valid_o = 0; 
            	evict_o = 0;
            	out_way_ind = way_ind_t'(0);
            	// Outputs required for HIT Detection
            	valid_o_plru = 0;
            	// Temporary data storage from SRAM Unit
            	temp_ram = data_plru'(0);
          
          	    // PLRU SRAM Request Signals                	
            	plru_request = 1'b0;
    		    plru_line_addr = line_addr'(0);
    		    plru_wdata = data_plru'(0);
    		
    		    // PLRU BIST Result valid signal
    		    plru_bist_res_valid_i = 0;
    		
    		    if (bist_i) begin
                	//To initialize the SRAM to Zeros
            		plru_request    = {Cfg.SetAssociativity{plru_gen_req}};
            		plru_we         = {Cfg.SetAssociativity{plru_gen_we}};
            		plru_line_addr  = plru_gen_index;
            		plru_wdata      = plru_gen_pattern;
            		if (ram_rvalid_q) begin
            			temp_ram              = plru_rdata;
            			plru_bist_res_valid_i = 1;
            		end
            	end

                if (hit_i && !valid_o_plru) begin
                    //we are a res_hit
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    	temp_ram = plru_rdata;
                    	thirtytwo_way_hit (res_indicator, temp_ram, thirtytwo_way_temp_ram);
                    	write_tc_sram(ram_index,thirtytwo_way_temp_ram);
                    	valid_o_plru = 1;
                    end
                end
                
                if (evict_i && !valid_o) begin
                    //find which way to evict
                    read_tc_sram(ram_index);
                    if (ram_rvalid_q) begin
                    temp_ram = plru_rdata;
                    thirtytwo_way_miss (temp_ram, spm_lock, out_way_ind, thirtytwo_way_temp_ram);
                    write_tc_sram(ram_index,thirtytwo_way_temp_ram);
                    valid_o = 1;
                    if ((tag_dirty_i & out_way_ind) != '0)
                    	evict_o = 1'b1;
                    end
                end

            end

        end      
    
    endcase

endgenerate 

endmodule
