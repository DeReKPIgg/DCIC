module detector (
    clk,
    rst_n,

    in_valid,
    flagChannelorData,
    InData,
    

    OutData,
    out_valid
    
);

//================================================================
// IO definition
//================================================================
input clk, rst_n;

input [89:0] InData;
input in_valid, flagChannelorData;

output reg [11:0] OutData;
output reg out_valid;

//================================================================
// storage
//================================================================
reg signed [14:0] z_tilde[0:5], z_tilde_nxt[0:5];
reg signed [14:0] R_row5, R_row4[0:1], R_row3[0:2], R_row2[0:3], R_row1[0:4], R_row0[0:5];
reg signed [14:0] R_row5_nxt, R_row4_nxt[0:1], R_row3_nxt[0:2], R_row2_nxt[0:3], R_row1_nxt[0:4], R_row0_nxt[0:5];

reg [1:0] leaf_row5[0:3], leaf_row4[0:7], leaf_row3[0:15], leaf_row2[0:31], leaf_row1[0:31], leaf_row0[0:31];
reg [1:0] leaf_row5_nxt[0:3], leaf_row4_nxt[0:7], leaf_row3_nxt[0:15], leaf_row2_nxt[0:31], leaf_row1_nxt[0:31], leaf_row0_nxt[0:31];
reg [23:0] leaf_value[0:31], leaf_value_nxt[0:31]; // integer part: 16 bits

reg [11:0] encode_symbol;

// DFF of leaf
always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        for(integer i=0; i<32; i=i+1) leaf_value[i] <= 0;

        for(integer i=0; i<32; i=i+1) leaf_row0[i] <= 0;
        for(integer i=0; i<32; i=i+1) leaf_row1[i] <= 0;
        for(integer i=0; i<32; i=i+1) leaf_row2[i] <= 0;
        for(integer i=0; i<16; i=i+1) leaf_row3[i] <= 0;
        for(integer i=0; i<8; i=i+1) leaf_row4[i] <= 0;
        for(integer i=0; i<4; i=i+1) leaf_row5[i] <= 0;

        for(integer i=0; i<6; i=i+1)begin
                z_tilde[i] <= 0;
                R_row0[i] <= 0;
        end
        for(integer i=0; i<5; i=i+1) R_row1[i] <= 0;
        for(integer i=0; i<4; i=i+1) R_row2[i] <= 0;
        for(integer i=0; i<3; i=i+1) R_row3[i] <= 0;
        for(integer i=0; i<2; i=i+1) R_row4[i] <= 0;
        R_row5 <= 0;
    end
    else begin
        for(integer i=0; i<32; i=i+1) leaf_value[i] <= leaf_value_nxt[i];

        for(integer i=0; i<32; i=i+1) leaf_row0[i] <= leaf_row0_nxt[i];
        for(integer i=0; i<32; i=i+1) leaf_row1[i] <= leaf_row1_nxt[i];
        for(integer i=0; i<32; i=i+1) leaf_row2[i] <= leaf_row2_nxt[i];
        for(integer i=0; i<16; i=i+1) leaf_row3[i] <= leaf_row3_nxt[i];
        for(integer i=0; i<8; i=i+1) leaf_row4[i] <= leaf_row4_nxt[i];
        for(integer i=0; i<4; i=i+1) leaf_row5[i] <= leaf_row5_nxt[i];

        for(integer i=0; i<6; i=i+1)begin

                if (in_valid && (cnt=='d4 || state==WAIT_NEW_DATA)) z_tilde[i] <= (~z_tilde_nxt[i]+1); // issue? z_tilde is actually negative z_tilde
                else z_tilde[i] <= z_tilde_nxt[i];

                R_row0[i] <= R_row0_nxt[i];
        end
        for(integer i=0; i<5; i=i+1) R_row1[i] <= R_row1_nxt[i];
        for(integer i=0; i<4; i=i+1) R_row2[i] <= R_row2_nxt[i];
        for(integer i=0; i<3; i=i+1) R_row3[i] <= R_row3_nxt[i];
        for(integer i=0; i<2; i=i+1) R_row4[i] <= R_row4_nxt[i];
        R_row5 <= R_row5_nxt;
    end
end

//================================================================
// Output logic
//================================================================
reg out_valid_nxt;
reg [11:0] OutData_nxt;

always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        OutData <= 0;
        out_valid <= 0;
    end
    else begin
        OutData <= OutData_nxt;
        out_valid <= out_valid_nxt;
    end
end

//================================================================
// FSM & counter
//================================================================
reg [5:0] cnt, cnt_nxt;

parameter IDLE = 0;
parameter READ_R_N_Z0 = 1;
parameter LAYER6 = 2;
parameter LAYER5 = 3;
parameter LAYER4 = 4;
parameter LAYER3 = 5;
parameter LAYER2 = 6;
parameter LAYER1 = 7;
parameter LAST = 8;
parameter WAIT_NEW_DATA = 9;

reg [3:0] state, NS;

always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        state <= IDLE;
        cnt <= 0;
    end
    else begin
        state <= NS;
        cnt <= cnt_nxt;
    end
end

//================================================================
// Arithmetic
// Layer: [4, 2, 2, 2, 1, 1]
// child combination: -3: 2'b11 -> signed 15'b 111111000011010
//                    -1: 2'b10 -> signed 15'b 111111101011110
//                     1: 2'b00 -> signed 15'b 000000010100010
//                     3: 2'b01 -> signed 15'b 000000111100110
//================================================================
reg [1:0] pre_multiplicant[0:4];
reg signed [14:0] multiplicant[0:4][0:1];
wire signed [28:0] multiplied[0:4];
wire signed [20:0] multiplied_truncated[0:4];

reg signed [20:0] multiplied_candidate[0:3], multiplied_candidate_nxt[0:3]; // DFF

reg signed [24:0] addend_mul[0:3][0:1]; // at same cycle with multipliers
wire signed [24:0] summation_mul[0:3];
reg signed [24:0] summation_mul_store[0:3]; // DFF

/* verilator lint_off UNOPTFLAT */
reg signed [24:0] addend[0:5][0:1] /* verilator split_var */; 
wire signed [24:0] summation[0:5] /* verilator split_var */;
/* verilator lint_off UNOPTFLAT */

wire signed [24:0] summation_conjugate[0:5];
wire [23:0] summation_abs[0:5];

reg [23:0] add2leaf[0:1][0:1];
wire  [23:0] sum2leaf[0:1];

always @(*) begin
    for(integer i=0; i<5; i=i+1) begin
        case (pre_multiplicant[i])
            // 2'b00: multiplicant[i][1] =  15'b111111000011010;
            // 2'b01: multiplicant[i][1] =  15'b111111101011110;
            // 2'b10: multiplicant[i][1] =  15'b000000010100010;
            // 2'b11: multiplicant[i][1] =  15'b000000111100110;
            2'b11: multiplicant[i][1] =  15'b111111100001101;
            2'b10: multiplicant[i][1] =  15'b111111110101111;
            2'b00: multiplicant[i][1] =  15'b000000001010001;
            2'b01: multiplicant[i][1] =  15'b000000011110011;
        endcase
    end
end

genvar i_ass;
generate
    // multiplication at 1st stage
    for(i_ass=0; i_ass<5; i_ass=i_ass+1) assign multiplied[i_ass] = multiplicant[i_ass][0] * multiplicant[i_ass][1];
    for(i_ass=0; i_ass<5; i_ass=i_ass+1) assign multiplied_truncated[i_ass] = multiplied[i_ass][28:8];

    // summation at 1st stage
    for(i_ass=0; i_ass<4; i_ass=i_ass+1) assign summation_mul[i_ass] = addend_mul[i_ass][0] + addend_mul[i_ass][1];

    // summation at 2nd stage
    for(i_ass=0; i_ass<6; i_ass=i_ass+1) assign summation[i_ass] = addend[i_ass][0] + addend[i_ass][1];
    for(i_ass=0; i_ass<6; i_ass=i_ass+1) assign summation_conjugate[i_ass] = ~summation[i_ass] + 1;
    for(i_ass=0; i_ass<6; i_ass=i_ass+1) assign summation_abs[i_ass] = summation[i_ass][24] ? summation_conjugate[i_ass][23:0] : summation[i_ass][23:0];
    
    // summation to leaf_value
    for(i_ass=0; i_ass<2; i_ass=i_ass+1) assign sum2leaf[i_ass] = add2leaf[i_ass][0] + add2leaf[i_ass][1];
endgenerate

always @(posedge clk, negedge rst_n) begin
    // store candidates [2'b00, 2'b01, 2'b10, 2'b11] .* first non-zero of each row
    if (!rst_n) for(integer i=0; i<4; i=i+1) multiplied_candidate[i] <= 0;
    else for(integer i=0; i<4; i=i+1) multiplied_candidate[i] <= multiplied_candidate_nxt[i];

    if (!rst_n) for(integer i=0; i<3; i=i+1) summation_mul_store[i] <= 0;
    else for(integer i=0; i<3; i=i+1) summation_mul_store[i] <= summation_mul[i];
end

//================================================================
// Sorting
// Find top2 minimum
// 1 -- -- 2 [6]--  -- 4 (don't care)  
//     |           |
// 2 -- -- 1 [5]   |      -- 3 (don't care) 
//                 |     |
// 3 -- -- 4 [8]--  -- 2 |     [3]  --  [1]
//     |                 |         |
// 4 -- -- 3 [7]          -- 1 [2]  --  [0]
//================================================================
reg [23:0] comparator_input[0:3];
wire [23:0] comparator_output[0:8] /* verilator split_var */; 
wire [1:0] comparator_symbol[0:8] /* verilator split_var */;

// {small, big}
// {small_symbol, big_symbol}
// 5 -> small
assign {comparator_output[5], comparator_output[6]} = (comparator_input[0] >= comparator_input[1]) ? {comparator_input[1], comparator_input[0]} : {comparator_input[0], comparator_input[1]};
assign {comparator_symbol[5], comparator_symbol[6]} = (comparator_input[0] >= comparator_input[1]) ? {2'b01, 2'b00} : {2'b00, 2'b01};

assign {comparator_output[7], comparator_output[8]} = (comparator_input[2] >= comparator_input[3]) ? {comparator_input[3], comparator_input[2]} : {comparator_input[2], comparator_input[3]};
assign {comparator_symbol[7], comparator_symbol[8]} = (comparator_input[2] >= comparator_input[3]) ? {2'b11, 2'b10} : {2'b10, 2'b11};


// smallest between 5 and 7
assign {comparator_output[0], comparator_output[4]} = (comparator_output[5] >= comparator_output[7]) ? {comparator_output[7], comparator_output[5]} : {comparator_output[5], comparator_output[7]};
assign {comparator_symbol[0], comparator_symbol[4]} = (comparator_output[5] >= comparator_output[7]) ? {comparator_symbol[7], comparator_symbol[5]} : {comparator_symbol[5], comparator_symbol[7]};

// smaller between 6 and 8
assign comparator_output[3] = (comparator_output[6] >= comparator_output[8]) ? comparator_output[8] : comparator_output[6];
assign comparator_symbol[3] = (comparator_output[6] >= comparator_output[8]) ? comparator_symbol[8] : comparator_symbol[6];
// second smallest 4 and 3
assign comparator_output[1] = (comparator_output[4] >= comparator_output[3]) ? comparator_output[3] : comparator_output[4];
assign comparator_symbol[1] = (comparator_output[4] >= comparator_output[3]) ? comparator_symbol[3] : comparator_symbol[4];

//================================================================
//========================   LOGIC    ============================ 
//================================================================

//================================================================
// FSM & counter logic
//================================================================
always @(*) begin
    // FSM
    case (state)
        IDLE: NS = in_valid ? READ_R_N_Z0 : IDLE;
        READ_R_N_Z0: NS = (cnt=='d4) ? LAYER6 : READ_R_N_Z0;
        LAYER6: NS = (cnt=='d1) ? LAYER5 : LAYER6;
        LAYER5: NS = (cnt=='d4) ? LAYER4 : LAYER5;
        LAYER4: NS = (cnt=='d8) ? LAYER3 : LAYER4; 
        LAYER3: NS = (cnt=='d16) ? LAYER2 : LAYER3;
        LAYER2: NS = (cnt=='d32) ? LAYER1 : LAYER2;
        LAYER1: NS = (cnt=='d32) ? LAST : LAYER1;
        LAST: NS = (cnt=='d11) ? WAIT_NEW_DATA : LAST;
        WAIT_NEW_DATA: NS = in_valid ? LAYER6 : WAIT_NEW_DATA;
        default: NS = IDLE;
    endcase
    
    // counter
    if (state==IDLE && in_valid) cnt_nxt = cnt + 1;
    else if (state==READ_R_N_Z0) cnt_nxt = (cnt=='d4) ? 0 : cnt + 1;
    else if (state==LAYER6) cnt_nxt = (cnt=='d1) ? 0 : cnt + 1;
    else if (state==LAYER5) cnt_nxt = (cnt=='d4) ? 0 : cnt + 1;
    else if (state==LAYER4) cnt_nxt = (cnt=='d8) ? 0 : cnt + 1; 
    else if (state==LAYER3) cnt_nxt = (cnt=='d16) ? 0 : cnt + 1;
    else if (state==LAYER2) cnt_nxt = (cnt=='d32) ? 0 : cnt + 1;
    else if (state==LAYER1) cnt_nxt = (cnt=='d32) ? 0 : cnt + 1;
    else if (state==LAST) cnt_nxt = (cnt=='d11) ? 0 : cnt + 1;
    else cnt_nxt = 0;
end

//================================================================
// InData to Register logic
//================================================================
always @(*) begin
    for(integer i=0; i<6; i=i+1)begin
        z_tilde_nxt[i] = z_tilde[i];
        R_row0_nxt[i] = R_row0[i];
    end

    for(integer i=0; i<5; i=i+1) R_row1_nxt[i] = R_row1[i];
    for(integer i=0; i<4; i=i+1) R_row2_nxt[i] = R_row2[i];
    for(integer i=0; i<3; i=i+1) R_row3_nxt[i] = R_row3[i];
    for(integer i=0; i<2; i=i+1) R_row4_nxt[i] = R_row4[i];
    R_row5_nxt = R_row5;

    if(in_valid && cnt=='d0 && state!=WAIT_NEW_DATA) {R_row0_nxt[0], R_row0_nxt[1], R_row0_nxt[2], R_row0_nxt[3], R_row0_nxt[4], R_row0_nxt[5]} = InData;
    else if(in_valid && cnt=='d1) {R_row1_nxt[0], R_row1_nxt[1], R_row1_nxt[2], R_row1_nxt[3], R_row1_nxt[4], R_row2_nxt[0]} = InData;
    else if(in_valid && cnt=='d2) {R_row2_nxt[1], R_row2_nxt[2], R_row2_nxt[3], R_row3_nxt[0], R_row3_nxt[1], R_row3_nxt[2]} = InData;
    else if(in_valid && cnt=='d3) {R_row4_nxt[0], R_row4_nxt[1], R_row5_nxt} = InData[89:45];
    
    if(in_valid && (cnt=='d4 || state==WAIT_NEW_DATA)) {z_tilde_nxt[0], z_tilde_nxt[1], z_tilde_nxt[2], z_tilde_nxt[3], z_tilde_nxt[4], z_tilde_nxt[5]} = InData;
end

//================================================================
// Layers logic
//================================================================
// multiplied_candidate
always @(*) begin
    // default
    for(integer i=0; i<4; i=i+1) multiplied_candidate_nxt[i] = multiplied_candidate[i];

    if ((state==LAYER5 && cnt == 'd0) || (state==LAYER5 && cnt == 'd4) || (state==LAYER4 && cnt == 'd8) || 
        (state==LAYER3 && cnt == 'd16) || (state==LAYER2 && cnt == 'd32)) begin
        multiplied_candidate_nxt[0] = multiplied_truncated[0];
        multiplied_candidate_nxt[1] = multiplied_truncated[1];
        multiplied_candidate_nxt[2] = multiplied_truncated[2];
        multiplied_candidate_nxt[3] = multiplied_truncated[3];
    end
end

// multiplicant & pre_mul 
always @(*) begin
    // default 
    for(integer i=0; i<5; i=i+1) multiplicant[i][0] = 0;
    for(integer i=0; i<5; i=i+1) pre_multiplicant[i] = 2'b00;

    // LAYER6
    if (state==LAYER6) begin
        multiplicant[0][0] = R_row5; pre_multiplicant[0] = 2'b00;
        multiplicant[1][0] = R_row5; pre_multiplicant[1] = 2'b01;
        multiplicant[2][0] = R_row5; pre_multiplicant[2] = 2'b10;
        multiplicant[3][0] = R_row5; pre_multiplicant[3] = 2'b11;
    end // LAYER5
    else if (state==LAYER5 && cnt == 'd0) begin // 0 -> 1
        multiplicant[4][0] = R_row4[1]; pre_multiplicant[4] = leaf_row5[0];

        multiplicant[0][0] = R_row4[0]; pre_multiplicant[0] = 2'b00;
        multiplicant[1][0] = R_row4[0]; pre_multiplicant[1] = 2'b01;
        multiplicant[2][0] = R_row4[0]; pre_multiplicant[2] = 2'b10;
        multiplicant[3][0] = R_row4[0]; pre_multiplicant[3] = 2'b11;
    end else if (state==LAYER5 && cnt == 'd1) begin // 2 -> 3
        multiplicant[4][0] = R_row4[1]; pre_multiplicant[4] = leaf_row5[1];
    end else if (state==LAYER5 && cnt == 'd2) begin // 4 -> 5
        multiplicant[4][0] = R_row4[1]; pre_multiplicant[4] = leaf_row5[2];
    end else if (state==LAYER5 && cnt == 'd3) begin // 6 -> 7
        multiplicant[4][0] = R_row4[1]; pre_multiplicant[4] = leaf_row5[3];
    end else if (state==LAYER5 && cnt == 'd4) begin // 6 -> 7
        multiplicant[0][0] = R_row3[0]; pre_multiplicant[0] = 2'b00;
        multiplicant[1][0] = R_row3[0]; pre_multiplicant[1] = 2'b01;
        multiplicant[2][0] = R_row3[0]; pre_multiplicant[2] = 2'b10;
        multiplicant[3][0] = R_row3[0]; pre_multiplicant[3] = 2'b11;
    end // LAYER4
    else if (state==LAYER4 && cnt == 'd0) begin // 0 -> 1
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[0];
    end else if (state==LAYER4 && cnt == 'd1) begin // 2 -> 3
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[1];
    end else if (state==LAYER4 && cnt == 'd2) begin // 4 -> 5
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[2];
    end else if (state==LAYER4 && cnt == 'd3) begin // 6 -> 7
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[3];
    end else if (state==LAYER4 && cnt == 'd4) begin // 8 -> 9
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[4];
    end else if (state==LAYER4 && cnt == 'd5) begin // 10 -> 11
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[5];
    end else if (state==LAYER4 && cnt == 'd6) begin // 12 -> 13
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[6];
    end else if (state==LAYER4 && cnt == 'd7) begin // 14 -> 15
        multiplicant[4][0] = R_row3[2]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row3[1]; pre_multiplicant[3] = leaf_row4[7];
    end else if (state==LAYER4 && cnt == 'd8) begin // 14 -> 15
        multiplicant[0][0] = R_row2[0]; pre_multiplicant[0] = 2'b00;
        multiplicant[1][0] = R_row2[0]; pre_multiplicant[1] = 2'b01;
        multiplicant[2][0] = R_row2[0]; pre_multiplicant[2] = 2'b10;
        multiplicant[3][0] = R_row2[0]; pre_multiplicant[3] = 2'b11;
    end // LAYER3
    else if (state==LAYER3 && cnt == 'd0) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[0];
    end else if (state==LAYER3 && cnt == 'd1) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[1];
    end else if (state==LAYER3 && cnt == 'd2) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[2];
    end else if (state==LAYER3 && cnt == 'd3) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[3];
    end else if (state==LAYER3 && cnt == 'd4) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[4];
    end else if (state==LAYER3 && cnt == 'd5) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[5];
    end else if (state==LAYER3 && cnt == 'd6) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[6];
    end else if (state==LAYER3 && cnt == 'd7) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[7];
    end else if (state==LAYER3 && cnt == 'd8) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[8];
    end else if (state==LAYER3 && cnt == 'd9) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[9];
    end else if (state==LAYER3 && cnt == 'd10) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[10];
    end else if (state==LAYER3 && cnt == 'd11) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[11];
    end else if (state==LAYER3 && cnt == 'd12) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[12];
    end else if (state==LAYER3 && cnt == 'd13) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[13];
    end else if (state==LAYER3 && cnt == 'd14) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[14];
    end else if (state==LAYER3 && cnt == 'd15) begin
        multiplicant[4][0] = R_row2[3]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row2[2]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row2[1]; pre_multiplicant[2] = leaf_row3[15];
    end else if (state==LAYER3 && cnt == 'd16) begin
        multiplicant[0][0] = R_row1[0]; pre_multiplicant[0] = 2'b00;
        multiplicant[1][0] = R_row1[0]; pre_multiplicant[1] = 2'b01;
        multiplicant[2][0] = R_row1[0]; pre_multiplicant[2] = 2'b10;
        multiplicant[3][0] = R_row1[0]; pre_multiplicant[3] = 2'b11;
    end // LAYER2
    else if (state==LAYER2 && cnt == 'd0) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[0];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[0];
    end else if (state==LAYER2 && cnt == 'd1) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[0];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[1];
    end else if (state==LAYER2 && cnt == 'd2) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[1];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[2];
    end else if (state==LAYER2 && cnt == 'd3) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[1];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[3];
    end else if (state==LAYER2 && cnt == 'd4) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[2];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[4];
    end else if (state==LAYER2 && cnt == 'd5) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[2];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[5];
    end else if (state==LAYER2 && cnt == 'd6) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[3];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[6];
    end else if (state==LAYER2 && cnt == 'd7) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[3];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[7];
    end else if (state==LAYER2 && cnt == 'd8) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[4];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[8];
    end else if (state==LAYER2 && cnt == 'd9) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[4];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[9];
    end else if (state==LAYER2 && cnt == 'd10) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[5];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[10];
    end else if (state==LAYER2 && cnt == 'd11) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[5];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[11];
    end else if (state==LAYER2 && cnt == 'd12) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[6];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[12];
    end else if (state==LAYER2 && cnt == 'd13) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[6];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[13];
    end else if (state==LAYER2 && cnt == 'd14) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[7];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[14];
    end else if (state==LAYER2 && cnt == 'd15) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[7];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[15];
    end else if (state==LAYER2 && cnt == 'd16) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[8];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[16];
    end else if (state==LAYER2 && cnt == 'd17) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[8];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[17];
    end else if (state==LAYER2 && cnt == 'd18) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[9];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[18];
    end else if (state==LAYER2 && cnt == 'd19) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[9];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[19];
    end else if (state==LAYER2 && cnt == 'd20) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[10];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[20];
    end else if (state==LAYER2 && cnt == 'd21) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[10];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[21];
    end else if (state==LAYER2 && cnt == 'd22) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[11];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[22];
    end else if (state==LAYER2 && cnt == 'd23) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[11];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[23];
    end else if (state==LAYER2 && cnt == 'd24) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[12];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[24];
    end else if (state==LAYER2 && cnt == 'd25) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[12];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[25];
    end else if (state==LAYER2 && cnt == 'd26) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[13];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[26];
    end else if (state==LAYER2 && cnt == 'd27) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[13];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[27];
    end else if (state==LAYER2 && cnt == 'd28) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[14];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[28];
    end else if (state==LAYER2 && cnt == 'd29) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[14];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[29];
    end else if (state==LAYER2 && cnt == 'd30) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[15];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[30];
    end else if (state==LAYER2 && cnt == 'd31) begin
        multiplicant[4][0] = R_row1[4]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row1[3]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row1[2]; pre_multiplicant[2] = leaf_row3[15];
        multiplicant[1][0] = R_row1[1]; pre_multiplicant[1] = leaf_row2[31];
    end else if (state==LAYER2 && cnt == 'd32) begin
        multiplicant[0][0] = R_row0[0]; pre_multiplicant[0] = 2'b00;
        multiplicant[1][0] = R_row0[0]; pre_multiplicant[1] = 2'b01;
        multiplicant[2][0] = R_row0[0]; pre_multiplicant[2] = 2'b10;
        multiplicant[3][0] = R_row0[0]; pre_multiplicant[3] = 2'b11;
    end // LAYER1
    else if (state==LAYER1 && cnt == 'd0) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[0];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[0];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[0];
    end else if (state==LAYER1 && cnt == 'd1) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[0];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[1];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[1];
    end else if (state==LAYER1 && cnt == 'd2) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[1];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[2];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[2];
    end else if (state==LAYER1 && cnt == 'd3) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[0];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[1];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[3];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[3];
    end else if (state==LAYER1 && cnt == 'd4) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[2];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[4];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[4];
    end else if (state==LAYER1 && cnt == 'd5) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[2];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[5];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[5];
    end else if (state==LAYER1 && cnt == 'd6) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[3];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[6];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[6];
    end else if (state==LAYER1 && cnt == 'd7) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[3];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[7];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[7];
    end else if (state==LAYER1 && cnt == 'd8) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[0];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[1];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[4];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[8];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[8];
    end else if (state==LAYER1 && cnt == 'd9) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[4];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[9];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[9];
    end else if (state==LAYER1 && cnt == 'd10) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[5];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[10];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[10];
    end else if (state==LAYER1 && cnt == 'd11) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[2];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[5];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[11];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[11];
    end else if (state==LAYER1 && cnt == 'd12) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[6];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[12];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[12];
    end else if (state==LAYER1 && cnt == 'd13) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[6];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[13];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[13];
    end else if (state==LAYER1 && cnt == 'd14) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[7];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[14];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[14];
    end else if (state==LAYER1 && cnt == 'd15) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[1];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[3];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[7];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[15];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[15];
    end else if (state==LAYER1 && cnt == 'd16) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[8];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[16];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[16];
    end else if (state==LAYER1 && cnt == 'd17) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[8];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[17];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[17];
    end else if (state==LAYER1 && cnt == 'd18) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[9];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[18];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[18];
    end else if (state==LAYER1 && cnt == 'd19) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[4];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[9];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[19];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[19];
    end else if (state==LAYER1 && cnt == 'd20) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[10];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[20];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[20];
    end else if (state==LAYER1 && cnt == 'd21) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[10];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[21];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[21];
    end else if (state==LAYER1 && cnt == 'd22) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[11];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[22];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[22];
    end else if (state==LAYER1 && cnt == 'd23) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[2];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[5];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[11];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[23];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[23];
    end else if (state==LAYER1 && cnt == 'd24) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[12];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[24];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[24];
    end else if (state==LAYER1 && cnt == 'd25) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[12];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[25];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[25];
    end else if (state==LAYER1 && cnt == 'd26) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[13];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[26];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[26];
    end else if (state==LAYER1 && cnt == 'd27) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[6];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[13];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[27];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[27];
    end else if (state==LAYER1 && cnt == 'd28) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[14];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[28];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[28];
    end else if (state==LAYER1 && cnt == 'd29) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[14];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[29];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[29];
    end else if (state==LAYER1 && cnt == 'd30) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[15];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[30];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[30];
    end else if (state==LAYER1 && cnt == 'd31) begin
        multiplicant[4][0] = R_row0[5]; pre_multiplicant[4] = leaf_row5[3];
        multiplicant[3][0] = R_row0[4]; pre_multiplicant[3] = leaf_row4[7];
        multiplicant[2][0] = R_row0[3]; pre_multiplicant[2] = leaf_row3[15];
        multiplicant[1][0] = R_row0[2]; pre_multiplicant[1] = leaf_row2[31];
        multiplicant[0][0] = R_row0[1]; pre_multiplicant[0] = leaf_row1[31];
    end
end

// addend_mul
always @(*) begin
    // default
    for(integer i=0; i<3; i=i+1)for(integer j=0; j<2; j=j+1) addend_mul[i][j] = 0;

    // if (state==LAYER6) begin
    //     addend_mul[0][0] = multiplied_truncated[0]; addend_mul[0][1] = z_tilde[5];
    //     addend_mul[1][0] = multiplied_truncated[1]; addend_mul[1][1] = z_tilde[5];
    //     addend_mul[2][0] = multiplied_truncated[2]; addend_mul[2][1] = z_tilde[5];
    //     addend_mul[3][0] = multiplied_truncated[3]; addend_mul[3][1] = z_tilde[5];
    // end 

    // LAYER5
    if (state==LAYER5)begin
        addend_mul[0][0] = multiplied_truncated[4]; addend_mul[0][1] = z_tilde[4]; // may cause problem with this
    end // LAYER4
    else if (state==LAYER4)begin
        addend_mul[0][0] = multiplied_truncated[4]; addend_mul[0][1] = multiplied_truncated[3];
        addend_mul[1][0] = z_tilde[3]; addend_mul[1][1] = 0;
    end // LAYER3
    else if (state==LAYER3)begin
        addend_mul[0][0] = multiplied_truncated[4]; addend_mul[0][1] = multiplied_truncated[3];
        addend_mul[1][0] = multiplied_truncated[2]; addend_mul[1][1] = z_tilde[2];
    end // LAYER2
    else if (state==LAYER2)begin
        addend_mul[0][0] = multiplied_truncated[4]; addend_mul[0][1] = multiplied_truncated[3];
        addend_mul[1][0] = multiplied_truncated[2]; addend_mul[1][1] = multiplied_truncated[1];
        addend_mul[2][0] = z_tilde[1]; addend_mul[2][1] = 0;
    end // LAYER1
    else if (state==LAYER1)begin
        addend_mul[0][0] = multiplied_truncated[4]; addend_mul[0][1] = multiplied_truncated[3];
        addend_mul[1][0] = multiplied_truncated[2]; addend_mul[1][1] = multiplied_truncated[1];
        addend_mul[2][0] = multiplied_truncated[0]; addend_mul[2][1] = z_tilde[0];
    end
    
end

// addend
always @(*) begin
    // default
    //for(integer i=0; i<6; i=i+1)for(integer j=0; j<2; j=j+1) addend[i][j] = 0;
    addend = '{default: '{default: 0}};

    // LAYER6
    if (state==LAYER6) begin
        addend[0][0] = multiplied_truncated[0]; addend[0][1] = z_tilde[5];
        addend[1][0] = multiplied_truncated[1]; addend[1][1] = z_tilde[5];
        addend[2][0] = multiplied_truncated[2]; addend[2][1] = z_tilde[5];
        addend[3][0] = multiplied_truncated[3]; addend[3][1] = z_tilde[5];
    end else if (state==LAYER5) begin // LAYER5
        addend[0][0] = summation_mul_store[0]; addend[0][1] = multiplied_candidate[0]; // 1st
        addend[1][0] = summation_mul_store[0]; addend[1][1] = multiplied_candidate[1]; // 1st
        addend[2][0] = summation_mul_store[0]; addend[2][1] = multiplied_candidate[2]; // 1st
        addend[3][0] = summation_mul_store[0]; addend[3][1] = multiplied_candidate[3]; // 1st
    end // LAYER4 || LAYER3
    else if (state==LAYER4 || state==LAYER3) begin
        addend[4][0] = summation_mul_store[0]; addend[4][1] = summation_mul_store[1]; // 1st

        addend[0][0] = summation[4]; addend[0][1] = multiplied_candidate[0]; // 2nd
        addend[1][0] = summation[4]; addend[1][1] = multiplied_candidate[1]; // 2nd
        addend[2][0] = summation[4]; addend[2][1] = multiplied_candidate[2]; // 2nd
        addend[3][0] = summation[4]; addend[3][1] = multiplied_candidate[3]; // 2nd
    end // LAYER2 || LAYER1
    else if (state==LAYER2 || state==LAYER1) begin
        addend[5][0] = summation_mul_store[0]; addend[5][1] = summation_mul_store[1]; // 1st
        addend[4][0] = summation[5]; addend[4][1] = summation_mul_store[2]; // 2nd

        addend[0][0] = summation[4]; addend[0][1] = multiplied_candidate[0]; // 3rd
        addend[1][0] = summation[4]; addend[1][1] = multiplied_candidate[1]; // 3rd
        addend[2][0] = summation[4]; addend[2][1] = multiplied_candidate[2]; // 3rd
        addend[3][0] = summation[4]; addend[3][1] = multiplied_candidate[3]; // 3rd
    end 

end

// comparator input
always @(*) begin
    // default
    for(integer i=0; i<4; i=i+1) comparator_input[i] = 24'b111111111111111111111111;

    if (state==LAYER5 || state==LAYER4 || state==LAYER3 || state==LAYER2 || state==LAYER1) begin
        comparator_input[0] = summation_abs[0]; // must be value derive from 2'b00
        comparator_input[1] = summation_abs[1]; // must be value derive from 2'b01
        comparator_input[2] = summation_abs[2]; // must be value derive from 2'b10
        comparator_input[3] = summation_abs[3]; // must be value derive from 2'b11
    end // LAST
    else if (state==LAST && cnt == 'd0) begin
        comparator_input[0] = leaf_value[0];
        comparator_input[1] = leaf_value[1];
        comparator_input[2] = leaf_value[2];
        comparator_input[3] = leaf_value[3];
    end else if (state==LAST && cnt == 'd1) begin
        comparator_input[0] = leaf_value[4];
        comparator_input[1] = leaf_value[5];
        comparator_input[2] = leaf_value[6];
        comparator_input[3] = leaf_value[7];
    end else if (state==LAST && cnt == 'd2) begin
        comparator_input[0] = leaf_value[8];
        comparator_input[1] = leaf_value[9];
        comparator_input[2] = leaf_value[10];
        comparator_input[3] = leaf_value[11];
    end else if (state==LAST && cnt == 'd3) begin
        comparator_input[0] = leaf_value[12];
        comparator_input[1] = leaf_value[13];
        comparator_input[2] = leaf_value[14];
        comparator_input[3] = leaf_value[15];
    end else if (state==LAST && cnt == 'd4) begin
        comparator_input[0] = leaf_value[16];
        comparator_input[1] = leaf_value[17];
        comparator_input[2] = leaf_value[18];
        comparator_input[3] = leaf_value[19];
    end else if (state==LAST && cnt == 'd5) begin
        comparator_input[0] = leaf_value[20];
        comparator_input[1] = leaf_value[21];
        comparator_input[2] = leaf_value[22];
        comparator_input[3] = leaf_value[23];
    end else if (state==LAST && cnt == 'd6) begin
        comparator_input[0] = leaf_value[24];
        comparator_input[1] = leaf_value[25];
        comparator_input[2] = leaf_value[26];
        comparator_input[3] = leaf_value[27];
    end else if (state==LAST && cnt == 'd7) begin
        comparator_input[0] = leaf_value[28];
        comparator_input[1] = leaf_value[29];
        comparator_input[2] = leaf_value[30];
        comparator_input[3] = leaf_value[31];
    end else if (state==LAST && cnt == 'd8) begin
        comparator_input[0] = leaf_value[3];
        comparator_input[1] = leaf_value[4];
        comparator_input[2] = leaf_value[5];
        comparator_input[3] = leaf_value[6];
    end else if (state==LAST && cnt == 'd9) begin
        comparator_input[0] = leaf_value[7];
        comparator_input[1] = leaf_value[8];
        comparator_input[2] = leaf_value[9];
        comparator_input[3] = leaf_value[10];
    end else if (state==LAST && cnt == 'd10) begin
        comparator_input[0] = leaf_value[3];
        comparator_input[1] = leaf_value[4];
    end
end


// add2leaf sum2leaf
always @(*) begin
    // default
    for(integer i=0; i<2; i=i+1)for(integer j=0; j<2; j=j+1) add2leaf[i][j] = 0;

    // LAYER5
    if (state==LAYER5 && cnt == 'd1) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[0];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[0];
    end else if (state==LAYER5 && cnt == 'd2) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[8];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[8];
    end else if (state==LAYER5 && cnt == 'd3) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[16];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[16];
    end else if (state==LAYER5 && cnt == 'd4) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[24];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[24];
    end // LAYER4
    else if (state==LAYER4 && cnt == 'd1) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[0];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[0];
    end else if (state==LAYER4 && cnt == 'd2) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[4];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[4];
    end else if (state==LAYER4 && cnt == 'd3) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[8];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[8];
    end else if (state==LAYER4 && cnt == 'd4) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[12];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[12];
    end else if (state==LAYER4 && cnt == 'd5) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[16];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[16];
    end else if (state==LAYER4 && cnt == 'd6) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[20];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[20];
    end else if (state==LAYER4 && cnt == 'd7) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[24];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[24];
    end else if (state==LAYER4 && cnt == 'd8) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[28];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[28];
    end // LAYER3
    else if (state==LAYER3 && cnt == 'd1) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[0];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[0];
    end else if (state==LAYER3 && cnt == 'd2) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[2];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[2];
    end else if (state==LAYER3 && cnt == 'd3) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[4];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[4];
    end else if (state==LAYER3 && cnt == 'd4) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[6];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[6];
    end else if (state==LAYER3 && cnt == 'd5) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[8];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[8];
    end else if (state==LAYER3 && cnt == 'd6) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[10];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[10];
    end else if (state==LAYER3 && cnt == 'd7) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[12];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[12];
    end else if (state==LAYER3 && cnt == 'd8) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[14];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[14];
    end else if (state==LAYER3 && cnt == 'd9) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[16];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[16];
    end else if (state==LAYER3 && cnt == 'd10) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[18];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[18];
    end else if (state==LAYER3 && cnt == 'd11) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[20];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[20];
    end else if (state==LAYER3 && cnt == 'd12) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[22];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[22];
    end else if (state==LAYER3 && cnt == 'd13) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[24];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[24];
    end else if (state==LAYER3 && cnt == 'd14) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[26];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[26];
    end else if (state==LAYER3 && cnt == 'd15) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[28];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[28];
    end else if (state==LAYER3 && cnt == 'd16) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[30];
        add2leaf[1][0] = comparator_output[1]; add2leaf[1][1] = leaf_value[30];
    end // LAYER2 || LAYER1
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd1) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[0];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd2) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[1];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd3) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[2];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd4) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[3];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd5) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[4];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd6) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[5];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd7) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[6];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd8) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[7];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd9) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[8];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd10) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[9];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd11) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[10];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd12) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[11];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd13) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[12];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd14) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[13];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd15) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[14];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd16) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[15];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd17) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[16];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd18) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[17];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd19) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[18];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd20) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[19];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd21) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[20];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd22) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[21];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd23) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[22];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd24) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[23];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd25) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[24];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd26) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[25];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd27) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[26];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd28) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[27];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd29) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[28];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd30) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[29];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd31) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[30];
    end else if ((state==LAYER2 || state==LAYER1) && cnt == 'd32) begin
        add2leaf[0][0] = comparator_output[0]; add2leaf[0][1] = leaf_value[31];
    end 
end

//================================================================
// Leaf logic
//================================================================
// leaf
always @(*) begin
    // default
    for(integer i=0; i<32; i=i+1) leaf_row0_nxt[i] = leaf_row0[i];
    for(integer i=0; i<32; i=i+1) leaf_row1_nxt[i] = leaf_row1[i];
    for(integer i=0; i<32; i=i+1) leaf_row2_nxt[i] = leaf_row2[i];
    for(integer i=0; i<16; i=i+1) leaf_row3_nxt[i] = leaf_row3[i];
    for(integer i=0; i<8; i=i+1) leaf_row4_nxt[i] = leaf_row4[i];
    for(integer i=0; i<4; i=i+1) leaf_row5_nxt[i] = leaf_row5[i];

    // LAYER6
    if (state==LAYER6) begin
        leaf_row5_nxt[0] = 2'b00;
        leaf_row5_nxt[1] = 2'b01;
        leaf_row5_nxt[2] = 2'b10;
        leaf_row5_nxt[3] = 2'b11;
    end // LAYER5
    else if (state==LAYER5 && cnt == 'd1) begin
        leaf_row4_nxt[0] = comparator_symbol[0];
        leaf_row4_nxt[1] = comparator_symbol[1];
    end else if (state==LAYER5 && cnt == 'd2) begin
        leaf_row4_nxt[2] = comparator_symbol[0];
        leaf_row4_nxt[3] = comparator_symbol[1];
    end else if (state==LAYER5 && cnt == 'd3) begin
        leaf_row4_nxt[4] = comparator_symbol[0];
        leaf_row4_nxt[5] = comparator_symbol[1];
    end else if (state==LAYER5 && cnt == 'd4) begin
        leaf_row4_nxt[6] = comparator_symbol[0];
        leaf_row4_nxt[7] = comparator_symbol[1];
    end // LAYER4
    else if (state==LAYER4 && cnt == 'd1) begin
        leaf_row3_nxt[0] = comparator_symbol[0];
        leaf_row3_nxt[1] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd2) begin
        leaf_row3_nxt[2] = comparator_symbol[0];
        leaf_row3_nxt[3] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd3) begin
        leaf_row3_nxt[4] = comparator_symbol[0];
        leaf_row3_nxt[5] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd4) begin
        leaf_row3_nxt[6] = comparator_symbol[0];
        leaf_row3_nxt[7] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd5) begin
        leaf_row3_nxt[8] = comparator_symbol[0];
        leaf_row3_nxt[9] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd6) begin
        leaf_row3_nxt[10] = comparator_symbol[0];
        leaf_row3_nxt[11] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd7) begin
        leaf_row3_nxt[12] = comparator_symbol[0];
        leaf_row3_nxt[13] = comparator_symbol[1];
    end else if (state==LAYER4 && cnt == 'd8) begin
        leaf_row3_nxt[14] = comparator_symbol[0];
        leaf_row3_nxt[15] = comparator_symbol[1];
    end // LAYER3
    else if (state==LAYER3 && cnt == 'd1) begin
        leaf_row2_nxt[0] = comparator_symbol[0];
        leaf_row2_nxt[1] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd2) begin
        leaf_row2_nxt[2] = comparator_symbol[0];
        leaf_row2_nxt[3] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd3) begin
        leaf_row2_nxt[4] = comparator_symbol[0];
        leaf_row2_nxt[5] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd4) begin
        leaf_row2_nxt[6] = comparator_symbol[0];
        leaf_row2_nxt[7] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd5) begin
        leaf_row2_nxt[8] = comparator_symbol[0];
        leaf_row2_nxt[9] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd6) begin
        leaf_row2_nxt[10] = comparator_symbol[0];
        leaf_row2_nxt[11] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd7) begin
        leaf_row2_nxt[12] = comparator_symbol[0];
        leaf_row2_nxt[13] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd8) begin
        leaf_row2_nxt[14] = comparator_symbol[0];
        leaf_row2_nxt[15] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd9) begin
        leaf_row2_nxt[16] = comparator_symbol[0];
        leaf_row2_nxt[17] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd10) begin
        leaf_row2_nxt[18] = comparator_symbol[0];
        leaf_row2_nxt[19] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd11) begin
        leaf_row2_nxt[20] = comparator_symbol[0];
        leaf_row2_nxt[21] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd12) begin
        leaf_row2_nxt[22] = comparator_symbol[0];
        leaf_row2_nxt[23] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd13) begin
        leaf_row2_nxt[24] = comparator_symbol[0];
        leaf_row2_nxt[25] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd14) begin 
        leaf_row2_nxt[26] = comparator_symbol[0];
        leaf_row2_nxt[27] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd15) begin
        leaf_row2_nxt[28] = comparator_symbol[0];
        leaf_row2_nxt[29] = comparator_symbol[1];
    end else if (state==LAYER3 && cnt == 'd16) begin
        leaf_row2_nxt[30] = comparator_symbol[0];
        leaf_row2_nxt[31] = comparator_symbol[1];
    end // LAYER2
    else if (state==LAYER2 && cnt == 'd1) leaf_row1_nxt[0] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd2) leaf_row1_nxt[1] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd3) leaf_row1_nxt[2] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd4) leaf_row1_nxt[3] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd5) leaf_row1_nxt[4] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd6) leaf_row1_nxt[5] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd7) leaf_row1_nxt[6] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd8) leaf_row1_nxt[7] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd9) leaf_row1_nxt[8] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd10) leaf_row1_nxt[9] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd11) leaf_row1_nxt[10] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd12) leaf_row1_nxt[11] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd13) leaf_row1_nxt[12] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd14) leaf_row1_nxt[13] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd15) leaf_row1_nxt[14] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd16) leaf_row1_nxt[15] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd17) leaf_row1_nxt[16] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd18) leaf_row1_nxt[17] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd19) leaf_row1_nxt[18] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd20) leaf_row1_nxt[19] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd21) leaf_row1_nxt[20] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd22) leaf_row1_nxt[21] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd23) leaf_row1_nxt[22] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd24) leaf_row1_nxt[23] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd25) leaf_row1_nxt[24] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd26) leaf_row1_nxt[25] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd27) leaf_row1_nxt[26] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd28) leaf_row1_nxt[27] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd29) leaf_row1_nxt[28] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd30) leaf_row1_nxt[29] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd31) leaf_row1_nxt[30] = comparator_symbol[0];
    else if (state==LAYER2 && cnt == 'd32) leaf_row1_nxt[31] = comparator_symbol[0];
    // LAYER1
    else if (state==LAYER1 && cnt == 'd1) leaf_row0_nxt[0] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd2) leaf_row0_nxt[1] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd3) leaf_row0_nxt[2] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd4) leaf_row0_nxt[3] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd5) leaf_row0_nxt[4] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd6) leaf_row0_nxt[5] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd7) leaf_row0_nxt[6] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd8) leaf_row0_nxt[7] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd9) leaf_row0_nxt[8] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd10) leaf_row0_nxt[9] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd11) leaf_row0_nxt[10] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd12) leaf_row0_nxt[11] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd13) leaf_row0_nxt[12] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd14) leaf_row0_nxt[13] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd15) leaf_row0_nxt[14] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd16) leaf_row0_nxt[15] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd17) leaf_row0_nxt[16] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd18) leaf_row0_nxt[17] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd19) leaf_row0_nxt[18] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd20) leaf_row0_nxt[19] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd21) leaf_row0_nxt[20] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd22) leaf_row0_nxt[21] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd23) leaf_row0_nxt[22] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd24) leaf_row0_nxt[23] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd25) leaf_row0_nxt[24] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd26) leaf_row0_nxt[25] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd27) leaf_row0_nxt[26] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd28) leaf_row0_nxt[27] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd29) leaf_row0_nxt[28] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd30) leaf_row0_nxt[29] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd31) leaf_row0_nxt[30] = comparator_symbol[0];
    else if (state==LAYER1 && cnt == 'd32) leaf_row0_nxt[31] = comparator_symbol[0];
    else if (state==LAST && cnt == 'd11) begin
        for(integer i=0; i<32; i=i+1) leaf_row0_nxt[i] = 0;
        for(integer i=0; i<32; i=i+1) leaf_row1_nxt[i] = 0;
        for(integer i=0; i<32; i=i+1) leaf_row2_nxt[i] = 0;
        for(integer i=0; i<16; i=i+1) leaf_row3_nxt[i] = 0;
        for(integer i=0; i<8; i=i+1) leaf_row4_nxt[i] = 0;
        for(integer i=0; i<4; i=i+1) leaf_row5_nxt[i] = 0;
    end
end

// leaf value
always @(*) begin
    // default
    for(integer i=0; i<32; i=i+1) leaf_value_nxt[i] = leaf_value[i];

    // LAYER6
    if (state==LAYER6 && cnt == 'd1) begin
        leaf_value_nxt[0] = summation_abs[0];
        leaf_value_nxt[8] = summation_abs[1];
        leaf_value_nxt[16] = summation_abs[2];
        leaf_value_nxt[24] = summation_abs[3];
    end // LAYER5
    else if (state==LAYER5 && cnt == 'd1) begin
        leaf_value_nxt[0] = sum2leaf[0];
        leaf_value_nxt[4] = sum2leaf[1];
    end else if (state==LAYER5 && cnt == 'd2) begin
        leaf_value_nxt[8] = sum2leaf[0];
        leaf_value_nxt[12] = sum2leaf[1];
    end else if (state==LAYER5 && cnt == 'd3) begin
        leaf_value_nxt[16] = sum2leaf[0];
        leaf_value_nxt[20] = sum2leaf[1];
    end else if (state==LAYER5 && cnt == 'd4) begin
        leaf_value_nxt[24] = sum2leaf[0];
        leaf_value_nxt[28] = sum2leaf[1];
    end // LAYER4
    else if (state==LAYER4 && cnt == 'd1) begin
        leaf_value_nxt[0] = sum2leaf[0];
        leaf_value_nxt[2] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd2) begin
        leaf_value_nxt[4] = sum2leaf[0];
        leaf_value_nxt[6] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd3) begin
        leaf_value_nxt[8] = sum2leaf[0];
        leaf_value_nxt[10] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd4) begin
        leaf_value_nxt[12] = sum2leaf[0];
        leaf_value_nxt[14] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd5) begin
        leaf_value_nxt[16] = sum2leaf[0];
        leaf_value_nxt[18] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd6) begin
        leaf_value_nxt[20] = sum2leaf[0];
        leaf_value_nxt[22] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd7) begin
        leaf_value_nxt[24] = sum2leaf[0];
        leaf_value_nxt[26] = sum2leaf[1];
    end else if (state==LAYER4 && cnt == 'd8) begin
        leaf_value_nxt[28] = sum2leaf[0];
        leaf_value_nxt[30] = sum2leaf[1];
    end // LAYER3
    else if (state==LAYER3 && cnt == 'd1) begin
        leaf_value_nxt[0] = sum2leaf[0];
        leaf_value_nxt[1] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd2) begin
        leaf_value_nxt[2] = sum2leaf[0];
        leaf_value_nxt[3] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd3) begin
        leaf_value_nxt[4] = sum2leaf[0];
        leaf_value_nxt[5] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd4) begin
        leaf_value_nxt[6] = sum2leaf[0];
        leaf_value_nxt[7] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd5) begin
        leaf_value_nxt[8] = sum2leaf[0];
        leaf_value_nxt[9] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd6) begin
        leaf_value_nxt[10] = sum2leaf[0];
        leaf_value_nxt[11] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd7) begin
        leaf_value_nxt[12] = sum2leaf[0];
        leaf_value_nxt[13] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd8) begin
        leaf_value_nxt[14] = sum2leaf[0];
        leaf_value_nxt[15] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd9) begin
        leaf_value_nxt[16] = sum2leaf[0];
        leaf_value_nxt[17] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd10) begin
        leaf_value_nxt[18] = sum2leaf[0];
        leaf_value_nxt[19] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd11) begin
        leaf_value_nxt[20] = sum2leaf[0];
        leaf_value_nxt[21] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd12) begin
        leaf_value_nxt[22] = sum2leaf[0];
        leaf_value_nxt[23] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd13) begin
        leaf_value_nxt[24] = sum2leaf[0];
        leaf_value_nxt[25] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd14) begin
        leaf_value_nxt[26] = sum2leaf[0];
        leaf_value_nxt[27] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd15) begin
        leaf_value_nxt[28] = sum2leaf[0];
        leaf_value_nxt[29] = sum2leaf[1];
    end else if (state==LAYER3 && cnt == 'd16) begin
        leaf_value_nxt[30] = sum2leaf[0];
        leaf_value_nxt[31] = sum2leaf[1];
    end // LAYER2 || LAYER1
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd1) leaf_value_nxt[0] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd2) leaf_value_nxt[1] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd3) leaf_value_nxt[2] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd4) leaf_value_nxt[3] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd5) leaf_value_nxt[4] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd6) leaf_value_nxt[5] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd7) leaf_value_nxt[6] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd8) leaf_value_nxt[7] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd9) leaf_value_nxt[8] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd10) leaf_value_nxt[9] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd11) leaf_value_nxt[10] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd12) leaf_value_nxt[11] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd13) leaf_value_nxt[12] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd14) leaf_value_nxt[13] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd15) leaf_value_nxt[14] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd16) leaf_value_nxt[15] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd17) leaf_value_nxt[16] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd18) leaf_value_nxt[17] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd19) leaf_value_nxt[18] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd20) leaf_value_nxt[19] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd21) leaf_value_nxt[20] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd22) leaf_value_nxt[21] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd23) leaf_value_nxt[22] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd24) leaf_value_nxt[23] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd25) leaf_value_nxt[24] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd26) leaf_value_nxt[25] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd27) leaf_value_nxt[26] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd28) leaf_value_nxt[27] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd29) leaf_value_nxt[28] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd30) leaf_value_nxt[29] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd31) leaf_value_nxt[30] = sum2leaf[0];
    else if ((state==LAYER2 || state==LAYER1) && cnt == 'd32) leaf_value_nxt[31] = sum2leaf[0];
    // LAST
    else if (state==LAST && cnt == 'd0) begin
        leaf_value_nxt[3] = comparator_output[0];
        leaf_value_nxt[0][1:0] = comparator_symbol[0]; 
    end
    else if (state==LAST && cnt == 'd1) begin
        leaf_value_nxt[4] = comparator_output[0];
        leaf_value_nxt[0][3:2] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd2) begin
        leaf_value_nxt[5] = comparator_output[0];
        leaf_value_nxt[0][5:4] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd3) begin
        leaf_value_nxt[6] = comparator_output[0];
        leaf_value_nxt[0][7:6] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd4) begin
        leaf_value_nxt[7] = comparator_output[0];
        leaf_value_nxt[0][9:8] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd5) begin
        leaf_value_nxt[8] = comparator_output[0];
        leaf_value_nxt[0][11:10] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd6) begin
        leaf_value_nxt[9] = comparator_output[0];
        leaf_value_nxt[0][13:12] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd7) begin
        leaf_value_nxt[10] = comparator_output[0];
        leaf_value_nxt[0][15:14] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd8) begin
        leaf_value_nxt[3] = comparator_output[0];
        leaf_value_nxt[0][17:16] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd9) begin
        leaf_value_nxt[4] = comparator_output[0];
        leaf_value_nxt[0][19:18] = comparator_symbol[0];
    end
    else if (state==LAST && cnt == 'd10) begin
        leaf_value_nxt[3] = comparator_output[0];
        leaf_value_nxt[0][21:20] = comparator_symbol[0];
    end 
    else if (state == LAST && cnt == 'd11) begin
        for(integer i=0; i<32; i=i+1) leaf_value_nxt[i] = 0;
    end
end

// encode symbol
always @(*) begin
    // default
    encode_symbol = 0;

    if (leaf_value_nxt[0][21:20]==2'b00) begin
        if (leaf_value_nxt[0][17:16]==4'b00) begin
            case (leaf_value_nxt[0][1:0])
                2'b00: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[15], leaf_row2[31], leaf_row1[31], leaf_row0[31]};
                2'b01: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[15], leaf_row2[30], leaf_row1[30], leaf_row0[30]};
                2'b10: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[14], leaf_row2[29], leaf_row1[29], leaf_row0[29]};
                2'b11: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[14], leaf_row2[28], leaf_row1[28], leaf_row0[28]};
            endcase
        end else if (leaf_value_nxt[0][17:16]==4'b01) begin
            case (leaf_value_nxt[0][3:2])
                2'b00: encode_symbol =  {leaf_row5[0], leaf_row4[1], leaf_row3[2], leaf_row2[4], leaf_row1[4], leaf_row0[4]};
                2'b01: encode_symbol =  {leaf_row5[0], leaf_row4[1], leaf_row3[2], leaf_row2[5], leaf_row1[5], leaf_row0[5]};
                2'b10: encode_symbol =  {leaf_row5[0], leaf_row4[1], leaf_row3[3], leaf_row2[6], leaf_row1[6], leaf_row0[6]};
                2'b11: encode_symbol =  {leaf_row5[0], leaf_row4[1], leaf_row3[3], leaf_row2[7], leaf_row1[7], leaf_row0[7]};
            endcase
        end else if (leaf_value_nxt[0][17:16]==4'b10) begin
            case (leaf_value_nxt[0][5:4])
                2'b00: encode_symbol =  {leaf_row5[1], leaf_row4[2], leaf_row3[4], leaf_row2[8], leaf_row1[8], leaf_row0[8]};
                2'b01: encode_symbol =  {leaf_row5[1], leaf_row4[2], leaf_row3[4], leaf_row2[9], leaf_row1[9], leaf_row0[9]};
                2'b10: encode_symbol =  {leaf_row5[1], leaf_row4[2], leaf_row3[5], leaf_row2[10], leaf_row1[10], leaf_row0[10]};
                2'b11: encode_symbol =  {leaf_row5[1], leaf_row4[2], leaf_row3[5], leaf_row2[11], leaf_row1[11], leaf_row0[11]};
            endcase
        end else if (leaf_value_nxt[0][17:16]==4'b11) begin
            case (leaf_value_nxt[0][7:6])
                2'b00: encode_symbol =  {leaf_row5[1], leaf_row4[3], leaf_row3[6], leaf_row2[12], leaf_row1[12], leaf_row0[12]};
                2'b01: encode_symbol =  {leaf_row5[1], leaf_row4[3], leaf_row3[6], leaf_row2[13], leaf_row1[13], leaf_row0[13]};
                2'b10: encode_symbol =  {leaf_row5[1], leaf_row4[3], leaf_row3[7], leaf_row2[14], leaf_row1[14], leaf_row0[14]};
                2'b11: encode_symbol =  {leaf_row5[1], leaf_row4[3], leaf_row3[7], leaf_row2[15], leaf_row1[15], leaf_row0[15]};
            endcase
        end
    end
    else if (leaf_value_nxt[0][21:20]==2'b01) begin
        if (leaf_value_nxt[0][19:18]==4'b00) begin
            case (leaf_value_nxt[0][9:8])
                2'b00: encode_symbol =  {leaf_row5[2], leaf_row4[4], leaf_row3[8], leaf_row2[16], leaf_row1[16], leaf_row0[16]};
                2'b01: encode_symbol =  {leaf_row5[2], leaf_row4[4], leaf_row3[8], leaf_row2[17], leaf_row1[17], leaf_row0[17]};
                2'b10: encode_symbol =  {leaf_row5[2], leaf_row4[4], leaf_row3[9], leaf_row2[18], leaf_row1[18], leaf_row0[18]};
                2'b11: encode_symbol =  {leaf_row5[2], leaf_row4[4], leaf_row3[9], leaf_row2[19], leaf_row1[19], leaf_row0[19]};
            endcase
        end else if (leaf_value_nxt[0][19:18]==4'b01) begin
            case (leaf_value_nxt[0][11:10])
                2'b00: encode_symbol =  {leaf_row5[2], leaf_row4[5], leaf_row3[10], leaf_row2[20], leaf_row1[20], leaf_row0[20]};
                2'b01: encode_symbol =  {leaf_row5[2], leaf_row4[5], leaf_row3[10], leaf_row2[21], leaf_row1[21], leaf_row0[21]};
                2'b10: encode_symbol =  {leaf_row5[2], leaf_row4[5], leaf_row3[11], leaf_row2[22], leaf_row1[22], leaf_row0[22]};
                2'b11: encode_symbol =  {leaf_row5[2], leaf_row4[5], leaf_row3[11], leaf_row2[23], leaf_row1[23], leaf_row0[23]};
            endcase
        end else if (leaf_value_nxt[0][19:18]==4'b10) begin
            case (leaf_value_nxt[0][13:12])
                2'b00: encode_symbol =  {leaf_row5[3], leaf_row4[6], leaf_row3[12], leaf_row2[24], leaf_row1[24], leaf_row0[24]};
                2'b01: encode_symbol =  {leaf_row5[3], leaf_row4[6], leaf_row3[12], leaf_row2[25], leaf_row1[25], leaf_row0[25]};
                2'b10: encode_symbol =  {leaf_row5[3], leaf_row4[6], leaf_row3[13], leaf_row2[26], leaf_row1[26], leaf_row0[26]};
                2'b11: encode_symbol =  {leaf_row5[3], leaf_row4[6], leaf_row3[13], leaf_row2[27], leaf_row1[27], leaf_row0[27]};
            endcase
        end else if (leaf_value_nxt[0][19:18]==4'b11) begin
            case (leaf_value_nxt[0][15:14])
                2'b00: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[14], leaf_row2[28], leaf_row1[28], leaf_row0[28]};
                2'b01: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[14], leaf_row2[29], leaf_row1[29], leaf_row0[29]};
                2'b10: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[15], leaf_row2[30], leaf_row1[30], leaf_row0[30]};
                2'b11: encode_symbol =  {leaf_row5[3], leaf_row4[7], leaf_row3[15], leaf_row2[31], leaf_row1[31], leaf_row0[31]};   
            endcase
        end
    end
end

// Output logic
always @(*) begin
    // default
    out_valid_nxt = 1'b0;
    OutData_nxt = 0;

    if (state == LAST && cnt == 'd10) begin
        out_valid_nxt = 1'b1;
        OutData_nxt = {encode_symbol[1:0],  encode_symbol[7:6], encode_symbol[3:2], encode_symbol[9:8], encode_symbol[5:4], encode_symbol[11:10]};
    end
end

endmodule