{$mode objfpc}
{$COPERATORS+}
{$modeswitch advancedrecords+}

uses
	SysUtils, math, FPImage, FPWritePNG;

const
	sz_x = 2048;
	sz_y = 2048;
	kern_size = 4;
	kern_lox = -kern_size; kern_hix = kern_size;
	kern_loy = -kern_size; kern_hiy = kern_size;

type
	TImagePixel = record
		rank: int32;
		fltr: int64;
	end;
	TImageLine = record
		px: array[-1..sz_x-1] of TImagePixel;
		maxtree: array[1..sz_x] of int32;
		maxp: Pint32;
		maxv: Pint64;
		procedure UpdateTree(l, r: sizeint);
	end;
	TKernelDraft = array[kern_lox..kern_hix, kern_loy..kern_hiy] of double;

var
	kern: array[kern_lox..kern_hix, kern_loy..kern_hiy] of int64;
	kernd: TKernelDraft;
	
	lines: array[0..sz_y-1] of TImageLine;
	horizmaxp: array[-1..sz_y-1] of int32;
	horizmaxv: array[-1..sz_y-1] of int64;
	verttree: array[1..sz_y] of int32;

procedure MkKernelFromDraft();
var
	x, y: sizeint;
	sum: double = 0.0;
begin
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			sum += abs(kernd[x,y]);
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			kern[x,y]:=round(high(int64)*0.9*kernd[x,y]/sum);
end;

procedure MkGaussDraft(sigma: double = 1.5);
var
	x, y: sizeint;
	invsgm: double;
begin
	invsgm := 1/(2*sigma*sigma);
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			kernd[x,y]:=exp(-(x*x+y*y)*invsgm);
end;

procedure MkGaussSincDraft(sigma: double = 1.5; sincr: double = 1.0);
var
	x, y, i: sizeint;
	dr : array[kern_lox-(kern_hix-kern_lox)..kern_hix+(kern_hix-kern_lox), kern_loy-(kern_hiy-kern_loy)..kern_hiy+(kern_hiy-kern_loy)] of double;
	dr2: array[kern_lox..kern_hix, kern_loy-(kern_hiy-kern_loy)..kern_hiy+(kern_hiy-kern_loy)] of double;
	invsgm, invscr: double;
begin
	invsgm := 1/(sigma*sigma);
	invscr := pi/sincr;
	for y:=kern_loy-(kern_hiy-kern_loy) to kern_hiy+(kern_hiy-kern_loy) do
		for x:=kern_lox-(kern_hix-kern_lox) to kern_hix+(kern_hix-kern_lox) do if (x = 0) and (y = 0) then dr[x,y]:=1 else
			dr[x,y]:=sin(hypot(x,y)*invscr)/(hypot(x,y)*invscr);
	for y:=kern_loy-(kern_hiy-kern_loy) to kern_hiy+(kern_hiy-kern_loy) do
		for x:=kern_lox to kern_hix do
			begin
				dr2[x,y]:=0.0;
				for i:=-(kern_hix-kern_lox) to (kern_hix-kern_lox) do
					dr2[x,y] += exp(-i*i*invsgm)*dr[x+i, y];
			end;
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			begin
				kernd[x,y]:=0.0;
				for i:=-(kern_hiy-kern_loy) to (kern_hiy-kern_loy) do
					kernd[x,y] += exp(-i*i*invsgm)*dr2[x, y+i];
			end;
end;

procedure MkInvsqrlenDraft(param: double = 1.0);
var
	x, y: sizeint;
begin
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			kernd[x,y]:=1/(param+x*x+y*y);
end;

procedure MkUniformDraft();
var
	x, y: sizeint;
begin
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			kernd[x,y]:=1;
end;

procedure MkXXXDraft();
var
	x, y: sizeint;
	r: double;
begin
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			begin
				r:=hypot(x,y)-5.0;
				if r>1 then
					kernd[x,y]:=0
				else if r<0 then
					kernd[x,y]:=1
				else
					kernd[x,y]:=0.5*(cos(pi*r)+1);
			end;
end;




procedure ApplyBlackman(alpha: double = 0.16; radius: double = 0.0);
var
	a0, a1, a2: double;
	r, rmax: double;
	x, y: sizeint;
begin
	a0:=(1-alpha)/2;
	a1:= 1       /2;
	a2:=   alpha /2;
	if (radius = 0.0) then
		rmax:=min(min(min(-kern_lox, -kern_loy), kern_hix), kern_hiy)+1
	else
		rmax:=radius+1;
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			begin
				r:=hypot(x,y)/rmax;
				if (r > 1) then
					kernd[x,y] := 0.0
				else
					kernd[x,y] *= a0 - a1*cos(pi*(1+r)) + a2*cos(2*pi*(1+r));
			end;
end;


procedure ApplyParzen(radius: double = 0.0);
var
	r, rmax: double;
	x, y: sizeint;
begin
	if (radius = 0.0) then
		rmax:=min(min(min(-kern_lox, -kern_loy), kern_hix), kern_hiy)+1
	else
		rmax:=radius+1;
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			begin
				r:=hypot(x,y)/rmax;
				if (r > 1) then
					kernd[x,y] := 0.0
				else if (r > 0.5) then
					kernd[x,y] := 2*(1-r)*(1-r)*(1-r)
				else
					kernd[x,y] := 1 - 6*r*r*(1-r)
			end;
end;


procedure InitImg();
var
	y: sizeint;
begin
	for y:=0 to sz_y-1 do
		begin
			lines[y].px[-1].fltr:=-7;
			lines[y].maxp:=@horizmaxp[y];
			lines[y].maxv:=@horizmaxv[y];
		end;
	horizmaxv[-1]:=-7;
	horizmaxp[-1]:=-1;
end;

procedure MkCheckerboard(toggle: boolean = false);
var
	x, y: sizeint;
	whl{, bll}: int64;
begin
	whl:=0;// bll:=0;
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			begin
				if ((x xor y) and 1) = 0 then
					whl+=kern[x, y]
				//else
				//	bll+=kern[x, y]
			end;
	for y:=0 to sz_y-1 do
		for x:=0 to sz_x-1 do
			begin
				//lines[y].px[x].ison := (((x xor y) and 1) = 1) xor toggle;
				if (((x xor y) and 1) = 1) xor toggle then
					lines[y].px[x].fltr := whl
				else
					lines[y].px[x].fltr := -7 //bll
			end;
end;

procedure MkFullField();
var
	x, y: sizeint;
	whl: int64;
begin
	whl:=0;
	for y:=kern_loy to kern_hiy do
		for x:=kern_lox to kern_hix do
			whl+=kern[x, y];
	for y:=0 to sz_y-1 do
		for x:=0 to sz_x-1 do
			lines[y].px[x].fltr := whl
end;

procedure MkJitter(am: int64 = 3000);
var
	x, y: sizeint;
begin
	for y:=0 to sz_y-1 do
		for x:=0 to sz_x-1 do
			lines[y].px[x].fltr += random(am);
end;



procedure TImageLine.UpdateTree(l, r: sizeint);
var
	i: sizeint;
begin
	if (l < 0) then
		begin
			self.UpdateTree(l+sz_x, sz_x-1);
			self.UpdateTree(0, r);
			exit;
		end;
	if (r >= sz_x) then
		begin
			self.UpdateTree(l, sz_x-1);
			self.UpdateTree(0, r-sz_x);
			exit;
		end;
	l := (l+sz_x) div 2;
	r := (r+sz_x) div 2;
	for i:=l to r do
		begin
			self.maxtree[i] := -1;
			if self.px[2*i-sz_x].fltr >= 0 then self.maxtree[i]:=2*i-sz_x;
			if (self.px[2*i+1-sz_x].fltr >= 0) and (self.px[2*i+1-sz_x].fltr > self.px[self.maxtree[i]].fltr) then self.maxtree[i]:=2*i+1-sz_x;
		end;
	l := l div 2;
	r := r div 2;
	while (l > 0) do
		begin
			for i:=l to r do
				begin
					self.maxtree[i] := self.maxtree[2*i];
					if (self.maxtree[2*i+1] >= 0) and (self.px[self.maxtree[2*i+1]].fltr > self.px[self.maxtree[2*i]].fltr) then self.maxtree[i]:=self.maxtree[2*i+1];
				end;
			l := l div 2;
			r := r div 2;
		end;
	self.maxp^ := self.maxtree[1];
	self.maxv^ := self.px[self.maxtree[1]].fltr;
end;

procedure UpdateVertTree(l, r: sizeint);
var
	i: sizeint;
begin
	if (l < 0) then
		begin
			UpdateVertTree(l+sz_y, sz_y-1);
			UpdateVertTree(0, r);
			exit;
		end;
	if (r >= sz_y) then
		begin
			UpdateVertTree(l, sz_y-1);
			UpdateVertTree(0, r-sz_y);
			exit;
		end;
	l := (l+sz_y) div 2;
	r := (r+sz_y) div 2;
	for i:=l to r do
		begin
			verttree[i] := -1;
			if (horizmaxp[2*i-sz_y] >= 0) then verttree[i]:=2*i-sz_y;
			if (horizmaxp[2*i+1-sz_y] >= 0) and (horizmaxv[2*i+1-sz_y] > horizmaxv[verttree[i]]) then verttree[i]:=2*i+1-sz_y;
		end;
	l := l div 2;
	r := r div 2;
	while (l > 0) do
		begin
			for i:=l to r do
				begin
					verttree[i] := verttree[2*i];
					if (verttree[2*i+1] >= 0) and (horizmaxv[verttree[2*i+1]] > horizmaxv[verttree[2*i]]) then verttree[i]:=verttree[2*i+1];
				end;
			l := l div 2;
			r := r div 2;
		end;
end;



procedure DePaint(x, y: sizeint);
var
	x0, y0: sizeint;
	i, j: sizeint;
begin
	lines[y].px[x].fltr:=-7;
	x += kern_lox;	if (x < 0) then x += sz_x;
	y += kern_loy;	if (y < 0) then y += sz_y;
	x0 := x; y0 := y;
	for j:=kern_loy to kern_hiy do
		begin
			x:=x0;
			for i:=kern_lox to kern_hix do
				begin
					lines[y].px[x].fltr -= kern[i,j];
					x += 1;
					if (x >= sz_x) then x -= sz_x;
				end;
			y += 1;
			if (y >= sz_y) then y -= sz_y;
		end;
	y:=y0;
	for j:=kern_loy to kern_hiy do
		begin
			lines[y].UpdateTree(x0, x0+(kern_hix-kern_lox));
			y += 1;
			if (y >= sz_y) then y -= sz_y;
		end;
	UpdateVertTree(y0, y0+(kern_hiy-kern_loy));
end;




procedure WritePNG(filename: ansistring);
var
	img: TFPMemoryImage;
	col: TFPColor;
	x, y: sizeint;
begin
	img := TFPMemoryImage.Create(sz_x, sz_y);
	img.UsePalette := false;
	col.alpha:=65535;
	for y := 0 to sz_y-1 do
		for x := 0 to sz_x-1 do
			begin
				col.red   := round(65535*lines[y].px[x].rank/(sz_x*sz_y));
				col.green := col.red;
				col.blue  := col.red;
				img.Colors[x,y] := col;
			end;
	img.SaveToFile(filename);
	img.Free;
end;

procedure WriteDebugImages(prefix: ansistring);
var
	img: TFPMemoryImage;
	col: TFPColor;
	x, y: sizeint;
	maxv: int64 = 1;
begin
	img := TFPMemoryImage.Create(sz_x, sz_y);
	img.UsePalette := false;
	col.alpha:=65535;
	for y := 0 to sz_y-1 do
		for x := 0 to sz_x-1 do
			begin
				if lines[y].px[x].fltr >= 0 then
					col.red := 65535
				else
					col.red := 0;
				col.green := col.red;
				col.blue  := col.red;
				img.Colors[x,y] := col;
			end;
	img.SaveToFile(prefix + '_ison.png');

	for y := 0 to sz_y-1 do
		for x := 0 to sz_x-1 do
			maxv := max(maxv, lines[y].px[x].fltr);

	for y := 0 to sz_y-1 do
		for x := 0 to sz_x-1 do
			begin
				if lines[y].px[x].fltr >= 0 then
					col.red := round(65535.0*lines[y].px[x].fltr/maxv)
				else
					col.red := 0;
				col.green := col.red;
				col.blue  := col.red;
				img.Colors[x,y] := col;
			end;
	img.SaveToFile(prefix + '_fltr.png');
end;



procedure WriteKernel();
var
	x, y: sizeint;
begin
	for y:=kern_loy to kern_hiy do
		begin
			for x:=kern_lox to kern_hix do
				write((kern[x,y] div 1000000000000):7);
			writeln;
		end;
end;


var
	i: sizeint;
	x, y: sizeint;

begin
	//randomize;
	
	InitImg;
	//MkXXXDraft;
	//MkGaussDraft(1.15);
	MkUniformDraft;
	//if ParamCount >= 2 then
	//	ApplyParzen(StrToFloat(ParamStr(2))/100);
	ApplyParzen(4);
	//ApplyBlackman(0.16, 3.5*2/3);
	//ApplyBlackman(2*1430/18608, 2.5);
	//ApplyBlackman(-200000, 3.0);
	MkKernelFromDraft;
	WriteKernel();

	MkFullField;
	MkJitter(3000);
	for i:=0 to sz_y-1 do
		lines[i].UpdateTree(0, sz_x-1);
	UpdateVertTree(0, sz_y-1);
	
	for i:=sz_x*sz_y downto 1 do
		begin
			y:=verttree[1];
			x:=lines[y].maxtree[1];
			//writeln(x:4,' ', y:4);
			lines[y].px[x].rank := i;
			DePaint(x, y);
		end;
	
	if ParamCount >= 1 then
		WritePNG(ParamStr(1))
	else
		WritePNG('out.png');
end.
