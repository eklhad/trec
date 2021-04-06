all : hexsol hp1 hp2 hp3 hp4 hept chiral trec 3dbox letterart drawit

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
	cc 3dbox.c -o 3dbox

#  for the two programs that use ImageMagick
IMFLAGS = -I/usr/include/ImageMagick-6 -I/usr/include/arm-linux-gnueabihf/ImageMagick-6 -DMAGICKCORE_QUANTUM_DEPTH=16 -DMAGICKCORE_HDRI_ENABLE=0
IMLIBS = /usr/lib/arm-linux-gnueabihf/libMagickWand-6.Q16.so.6 /usr/lib/arm-linux-gnueabihf/libMagickCore-6.Q16.so.6

letterart : letterart.c
	cc $(IMFLAGS) letterart.c $(IMLIBS) -o letterart

drawit : drawit.c
	cc $(IMFLAGS) drawit.c $(IMLIBS) -o drawit

clean:
	@rm -f hexsol hp1 hp2 hp3 hp4 hept chiral trec letterart drawit

install : trec chiral letterart
	install -m 0755 $< /usr/local/bin

