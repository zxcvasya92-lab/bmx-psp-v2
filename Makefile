TARGET = bmxlite
OBJS = main.o

CFLAGS = -O2 -G0 -Wall -std=gnu99
CXXFLAGS = $(CFLAGS) -fno-exceptions -fno-rtti
ASFLAGS = $(CFLAGS)

LIBS = -lpspdebug -lpspgum -lpspgu -lpspge -lpspdisplay -lpspctrl -lm

EXTRA_TARGETS = EBOOT.PBP
PSP_EBOOT_TITLE = BMX Streets Lite

PSPSDK = $(shell psp-config --pspsdk-path)
include $(PSPSDK)/lib/build.mak
