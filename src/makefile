all : hexsol hp1 hp2 hp3 hp4 hept chiral trec 3dbox piece-encode piece-decode

hexsol : hexsol.c
	cc hexsol.c -o hexsol

hp1 : hp1.c
	cc hp1.c -o hp1

hp2 : hp2.c
	cc hp2.c -o hp2

hp3 : hp3.c
	cc hp3.c -o hp3

hp4 : hp4.c
	cc hp4.c -o hp4

hept : hept.c
	cc hept.c -o hept

chiral : chiral.c
	cc chiral.c -o chiral

trec : trec.c
	cc -O trec.c -o trec -lpthread

3dbox : 3dbox.c
	cc -O 3dbox.c -o 3dbox

clean:
	@rm -f hexsol hp1 hp2 hp3 hp4 hept chiral trec  3dbox

