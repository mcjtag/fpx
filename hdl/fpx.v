`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Engineer: Dmitry Matyunin (https://github.com/mcjtag)
// 
// Create Date: 26.08.2024 18:42:22
// Design Name: fpx
// Description: A parameterizable floating point operations
//  IEEE754 standard settings:
//	FP16 : NUM_W = 16,  EXP_W = 5,  MAN_W = 10  (Half-precision)
//	FP32 : NUM_W = 32,  EXP_W = 8,  MAN_W = 23  (Single-precision)
//	FP64 : NUM_W = 64,  EXP_W = 11, MAN_W = 52  (Double-precision)
//	FP128: NUM_W = 128, EXP_W = 15, MAN_W = 112 (Quadruple-precision)
//	FP256: NUM_W = 256, EXP_W = 19, MAN_W = 236 (Octuple-precision)
// License: MIT
//  Copyright (c) 2024 Dmitry Matyunin
//  Permission is hereby granted, free of charge, to any person obtaining a copy
//  of this software and associated documentation files (the "Software"), to deal
//  in the Software without restriction, including without limitation the rights
//  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//  copies of the Software, and to permit persons to whom the Software is
//  furnished to do so, subject to the following conditions:
//
//  The above copyright notice and this permission notice shall be included in
//  all copies or substantial portions of the Software.
//
//  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY
//  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
//  THE SOFTWARE.
// 
//////////////////////////////////////////////////////////////////////////////////

//
// Floating Point Multiplication
//
module fpx_mul #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [NUM_W-1:0]a,	// Operand A
	input wire [NUM_W-1:0]b,	// Operand B
	output reg [NUM_W-1:0]p		// Product P=A*B
);

reg [MAN_W:0]op_a, op_b;
reg [2*(MAN_W+1)-1:0]p_mul;
reg [EXP_W:0]exp_s;
reg exc, sign, norm;
reg [2*(MAN_W+1)-1:0]p_norm;
reg [MAN_W-1:0]p_man;
reg [EXP_W:0]exp;
reg zero, ovf, unf;
reg [NUM_W-1:0]p_w;

always @(*) begin
	op_a = (|a[NUM_W-2-:EXP_W]) ? {1'b1,a[MAN_W-1:0]} : {1'b0,a[MAN_W-1:0]};
	op_b = (|b[NUM_W-2-:EXP_W]) ? {1'b1,b[MAN_W-1:0]} : {1'b0,b[MAN_W-1:0]};
	p_mul = op_a * op_b;
	exp_s = a[NUM_W-2-:EXP_W] + b[NUM_W-2-:EXP_W];
	exc = (&a[NUM_W-2-:EXP_W]) | (&b[NUM_W-2-:EXP_W]);
	sign = (a[NUM_W-1] ^ b[NUM_W-1]); //
	norm = p_mul[2*(MAN_W+1)-1] ? 1'b1 : 1'b0;
	p_norm = norm ? p_mul : p_mul << 1;
	p_man = p_norm[2*(MAN_W+1)-2-:MAN_W] + (p_norm[MAN_W] & (|p_norm[MAN_W-1:0]));
	exp = exp_s - (2**(EXP_W-1)-1) + norm; //
	zero = exc ? 1'b0 : (p_mul == 'd0) ? 1'b1 : 1'b0;
	ovf = ((exp[EXP_W] & !exp[EXP_W-1]) & !zero) ? 1'b1 : 1'b0;
	unf = ((exp[EXP_W] &  exp[EXP_W-1]) & !zero) ? 1'b1 : 1'b0;
	p_w = exc  ? {1'b0, {EXP_W{1'b1}}, 1'b1, {(MAN_W-1){1'b0}}} : 
		  zero ? {sign, {(NUM_W-1){1'b0}}} : 
		  ovf  ? {sign, {EXP_W{1'b1}}, {MAN_W{1'b0}}} : 
		  unf  ? {sign, {(NUM_W-1){1'b0}}} : 
				 {sign, exp[EXP_W-1:0], p_man};
end

generate if (REGOUT) begin
	always @(posedge clk) begin
		p <= p_w;
	end
end else begin
	always @(*) begin
		p = p_w;
	end
end endgenerate

endmodule

//
// Floating Point Addition
//
module fpx_add #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [NUM_W-1:0]a,	// Operand A
	input wire [NUM_W-1:0]b,	// Operand B
	output reg [NUM_W-1:0]p,	// Product P=A+B / P=A-B
	input wire sub				// Subraction: 0 - add, 1 - subtract
);

localparam EXT = 1;

reg exc, op_sub, cmp_en, sign, perf;
reg [NUM_W-1:0]op_a, op_b, p_w;
reg [MAN_W+EXT:0]sign_a, sign_b, sign_b_add;
reg [MAN_W+EXT:0]sign_sub_c;
reg [EXP_W-1:0]exp_diff, exp_b_add, exp_s;
reg [MAN_W+1+EXT:0]sign_add, sign_sub, sign_s;
reg [NUM_W-2:0]add_sum, sub_sum;
integer i, j;

always @(*) begin
	{cmp_en,op_a,op_b} = (a[NUM_W-2:0] < b[NUM_W-2:0]) ? {1'b1,b,a} : {1'b0,a,b};
	exc = (&op_a[NUM_W-2-:EXP_W]) | (&op_b[NUM_W-2-:EXP_W]);
	sign = sub ? cmp_en ? !op_a[NUM_W-1] : op_a[NUM_W-1] : op_a[NUM_W-1] ;
	op_sub = sub ? ~(op_a[NUM_W-1] ^ op_b[NUM_W-1]) : (op_a[NUM_W-1] ^ op_b[NUM_W-1]);
	sign_a = (|op_a[NUM_W-2-:EXP_W]) ? {1'b1,op_a[MAN_W-1:0],{EXT{1'b0}}} : {1'b0,op_a[MAN_W-1:0],{EXT{1'b0}}};
	sign_b = (|op_b[NUM_W-2-:EXP_W]) ? {1'b1,op_b[MAN_W-1:0],{EXT{1'b0}}} : {1'b0,op_b[MAN_W-1:0],{EXT{1'b0}}};
	exp_diff = op_a[NUM_W-2-:EXP_W] - op_b[NUM_W-2-:EXP_W];
	sign_b_add = sign_b >> exp_diff;
	exp_b_add = op_b[NUM_W-2-:EXP_W] + exp_diff;
	perf = (op_a[NUM_W-2-:EXP_W] == exp_b_add); //
	sign_add = perf ? (sign_a + sign_b_add) : {(MAN_W+2+EXT){1'b0}};
	add_sum[MAN_W-1:0] = sign_add[MAN_W+1+EXT] ? 
		sign_add[MAN_W+EXT  :1+EXT] + sign_add[EXT] : sign_add[MAN_W-1+EXT:0+EXT] + sign_add[EXT-1];
	add_sum[NUM_W-2-:EXP_W] = sign_add[MAN_W+1+EXT] ? (1'b1 + op_a[NUM_W-2-:EXP_W]) : op_a[NUM_W-2-:EXP_W]; //
	sign_sub_c = ~sign_b_add + 1'b1;
	sign_sub = perf ? (sign_a + sign_sub_c) : {(MAN_W+2){1'b0}};
	if (sign_sub[MAN_W+1+EXT] == 1'b1) begin
		j = 0;
		for (i = 0; i < MAN_W+1; i = i + 1) begin
			if (sign_sub[i+EXT] == 1'b1) begin
				j = i+1;
			end
		end
		sign_s = (sign_sub << (MAN_W+1-j));
		exp_s = op_a[NUM_W-2-:EXP_W] - (MAN_W+1-j);
	end else begin
		sign_s = sign_sub;
		exp_s = op_a[NUM_W-2-:EXP_W];
	end
	sub_sum = {exp_s, sign_s[MAN_W-1+EXT:0+EXT]};
	p_w = exc    ? {1'b0, {EXP_W{1'b1}}, 1'b1, {(MAN_W-1){1'b0}}} :
		  op_sub ? {sign, sub_sum} : 
		           {sign, add_sum};
end

generate if (REGOUT) begin
	always @(posedge clk) begin
		p <= p_w;
	end
end else begin
	always @(*) begin
		p = p_w;
	end
end endgenerate

endmodule

//
// Floating Point to Integer Conversion
//
module fpx_rtoi #(
	parameter NUM_W = 32,		// Number Width
	parameter NUM_Q = 0,		// Number Q-format (fraction width)
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [NUM_W-1:0]a,	// Operand A
	output reg [NUM_W-1:0]p		// Product P=int(A)
);

reg [NUM_W-1:0]sign_a, p_w;
reg [EXP_W:0]exp;
reg sign;
integer i;


always @(*) begin
	sign_a = {1'b1, a[MAN_W-1:0], {EXP_W{1'b0}}};
	exp = a[NUM_W-2-:EXP_W] - (2**(EXP_W-1)-1);
	sign = a[NUM_W-1];
	if ($signed(exp) == -(2**(EXP_W-1)-1)) begin
		p_w = {NUM_W{1'b0}};
	end else if ($signed(exp) > (NUM_W-1)) begin
 		p_w = {1'b1, {(NUM_W-1){1'b0}}};
	end else begin
		for (i = 0; i < (NUM_W-1); i = i + 1) begin
			if (($signed(exp) < (NUM_W-NUM_Q-1)) && sign_a) begin
				exp = exp + 1;
				sign_a = sign_a >> 1;
        	end 
        end
		if (sign_a[NUM_W-1]) begin
			p_w = sign ? {1'b1, {(NUM_W-1){1'b0}}} : {1'b0, {(NUM_W-1){1'b1}}};
		end else begin
			p_w = sign ? -sign_a : sign_a;
		end
	end
end

generate if (REGOUT) begin
	always @(posedge clk) begin
		p <= p_w;
	end
end else begin
	always @(*) begin
		p = p_w;
	end
end endgenerate

endmodule

//
// Integer to Floating Point Conversion
//
module fpx_itor #(
	parameter NUM_W = 32,		// Number Width
	parameter NUM_Q = 0,		// Number Q-format (fraction width)
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [NUM_W-1:0]a,	// Operand A
	output reg [NUM_W-1:0]p		// Product P=float(A)
);

reg [NUM_W-1:0]p_w;
reg [MAN_W:0]sign_a;
reg [EXP_W-1:0]exp_s, exp;
reg sign;
integer i;

always @(*) begin
	if (a == 0) begin
		sign = 1'b0;
		sign_a = {(MAN_W+1){1'b0}};
		exp = -(2**(EXP_W-1)-1);
	end else begin
		sign = a[NUM_W-1];
		exp = NUM_W-NUM_Q-1;
        {sign_a, exp_s} = a[NUM_W-1] ? -a : a;
        for (i = 0; i < (NUM_W-1); i = i + 1) begin
        	if (sign_a[MAN_W] == 1'b0) begin
        		exp = exp - 1;
				sign_a = {sign_a[MAN_W-1:0], exp_s[EXP_W-1]};
				exp_s = exp_s << 1;
        	end
        end
		if (exp_s[EXP_W-1] & (exp_s[EXP_W-2] | (exp_s[EXP_W-3:0] != {(EXP_W-2){1'b0}}) | sign_a[0])) begin
			if (sign_a == {(MAN_W+1){1'b1}}) begin
				exp = exp + 1;
			end
			sign_a = sign_a + 1;
       	end
	end
	p_w[MAN_W-1:0] = sign_a[MAN_W-1:0];
	p_w[NUM_W-2-:EXP_W] = exp + (2**(EXP_W-1)-1);
	p_w[NUM_W-1] = sign;
end

generate if (REGOUT) begin
	always @(posedge clk) begin
		p <= p_w;
	end
end else begin
	always @(*) begin
		p = p_w;
	end
end endgenerate

endmodule

//
// Floating Point Absolute Value
//
module fpx_abs #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [NUM_W-1:0]a,	// Operand A
	output reg [NUM_W-1:0]p		// Product P=abs(A)
);

generate if (REGOUT) begin
	always @(posedge clk) begin
		p <= {1'b0, a[NUM_W-2:0]};
	end
end else begin
	always @(*) begin
		p = {1'b0, a[NUM_W-2:0]};
	end
end endgenerate

endmodule

//
// Integer to Floating Point Comparison
//
module fpx_cmp #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [NUM_W-1:0]a,	// Operand A
	input wire [NUM_W-1:0]b,	// Operand B
	output reg gt,				// A > B
	output reg eq,				// A = B
	output reg lt				// A < B 
);

reg exc;
reg s_lt, s_gt, s_eq;
reg e_lt, e_gt, e_eq;
reg m_lt, m_gt, m_eq;
reg p_gt, p_eq, p_lt;

// Stage 0
always @(*) begin
	exc = (&a[NUM_W-2-:EXP_W]) | (&b[NUM_W-2-:EXP_W]);
	{s_lt, s_gt, s_eq} = {a[NUM_W-1] < b[NUM_W-1], a[NUM_W-1] > b[NUM_W-1], a[NUM_W-1] == b[NUM_W-1]};
	{e_lt, e_gt, e_eq} = {a[NUM_W-2-:EXP_W] < b[NUM_W-2-:EXP_W], a[NUM_W-2-:EXP_W] > b[NUM_W-2-:EXP_W], a[NUM_W-2-:EXP_W] == b[NUM_W-2-:EXP_W]};
	{m_lt, m_gt, m_eq} = {a[MAN_W-1:0] < b[MAN_W-1:0], a[MAN_W-1:0] > b[MAN_W-1:0], a[MAN_W-1:0] == b[MAN_W-1:0]};
	if (exc == 1'b1) begin
		{p_gt, p_eq, p_lt} = 3'b000;
	end else begin
		p_gt = (s_lt | (e_gt & s_eq) | (m_gt & e_eq & s_eq)) ^ (a[NUM_W-1] & s_eq);
		p_eq = e_eq & m_eq & s_eq;
		p_lt = (s_gt | (e_lt & s_eq) | (m_lt & e_eq & s_eq)) ^ (a[NUM_W-1] & s_eq);
	end
end

generate if (REGOUT) begin
	always @(posedge clk) begin
		{gt, eq, lt} <= {p_gt, p_eq, p_lt};
	end
end else begin
	always @(*) begin
		{gt, eq, lt} = {p_gt, p_eq, p_lt};
	end
end endgenerate

endmodule

//
// Floating Point Complex Multiplication
//
module fpx_cmul #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [2*NUM_W-1:0]a,	// Complex Operand A:     REAL=a[NUM_W-1-:NUM_W], IMAG=a[2*NUM_W-1-:NUM_W]
	input wire [2*NUM_W-1:0]b,	// Complex Operand B:     REAL=b[NUM_W-1-:NUM_W], IMAG=b[2*NUM_W-1-:NUM_W]
	output wire [2*NUM_W-1:0]p	// Complex Product P=A*B: REAL=p[NUM_W-1-:NUM_W], IMAG=p[2*NUM_W-1-:NUM_W]
);

wire [NUM_W-1:0]re[1:0];
wire [NUM_W-1:0]im[1:0];

fpx_mul #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_mul_re0 (.clk(clk),.a(a[NUM_W-1-:NUM_W]),  .b(b[NUM_W-1-:NUM_W]),  .p(re[0]));
fpx_mul #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_mul_re1 (.clk(clk),.a(a[2*NUM_W-1-:NUM_W]),.b(b[2*NUM_W-1-:NUM_W]),.p(re[1]));
fpx_mul #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_mul_im0 (.clk(clk),.a(a[2*NUM_W-1-:NUM_W]),.b(b[NUM_W-1-:NUM_W]),  .p(im[0]));
fpx_mul #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_mul_im1 (.clk(clk),.a(a[NUM_W-1-:NUM_W]),  .b(b[2*NUM_W-1-:NUM_W]),.p(im[1]));

fpx_add #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_add_re  (.clk(clk),.a(re[0]),.b(re[1]),.sub(1'b1),.p(p[NUM_W-1-:NUM_W]));
fpx_add #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_add_im  (.clk(clk),.a(im[0]),.b(im[1]),.sub(1'b0),.p(p[2*NUM_W-1-:NUM_W]));

endmodule

//
// Floating Point Complex Addition
//
module fpx_cadd #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [2*NUM_W-1:0]a,	// Complex Operand A:     REAL=a[NUM_W-1-:NUM_W], IMAG=a[2*NUM_W-1-:NUM_W]
	input wire [2*NUM_W-1:0]b,	// Complex Operand B:     REAL=b[NUM_W-1-:NUM_W], IMAG=b[2*NUM_W-1-:NUM_W]
	output wire [2*NUM_W-1:0]p,	// Complex Product P=A*B: REAL=p[NUM_W-1-:NUM_W], IMAG=p[2*NUM_W-1-:NUM_W]
	input wire sub				// Subraction: 0 - add, 1 - subtract
);

fpx_add #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_add_re (.clk(clk),.a(a[NUM_W-1-:NUM_W]),  .b(b[NUM_W-1-:NUM_W]),  .sub(sub),.p(p[NUM_W-1-:NUM_W]));
fpx_add #(.NUM_W(NUM_W), .EXP_W(EXP_W), .MAN_W(MAN_W), .REGOUT(REGOUT)) fpx_add_im (.clk(clk),.a(a[2*NUM_W-1-:NUM_W]),.b(b[2*NUM_W-1-:NUM_W]),.sub(sub),.p(p[2*NUM_W-1-:NUM_W]));

endmodule

//
// Floating Point Complex Conjugation
//
module fpx_conj #(
	parameter NUM_W = 32,		// Number Width
	parameter EXP_W = 8,		// Exponent Width
	parameter MAN_W = 23,		// Mantissa Width
	parameter REGOUT = 0		// Output Trigger (1 - enable, 0 - disable)
)
(
	input wire clk,
	input wire [2*NUM_W-1:0]a,	// Complex Operand A:               REAL=a[NUM_W-1-:NUM_W], IMAG=a[2*NUM_W-1-:NUM_W]
	output reg [2*NUM_W-1:0]p	// Complex Product P=Re{A}-1*Im{B}: REAL=p[NUM_W-1-:NUM_W], IMAG=p[2*NUM_W-1-:NUM_W]
);

generate if (REGOUT) begin
	always @(posedge clk) begin
		p <= {~a[2*NUM_W-1], a[2*NUM_W-2-:NUM_W-1], a[NUM_W-1-:NUM_W]};
	end
end else begin
	always @(*) begin
		p = {~a[2*NUM_W-1], a[2*NUM_W-2-:NUM_W-1], a[NUM_W-1-:NUM_W]};
	end
end endgenerate

endmodule
