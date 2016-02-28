TARGET=CMP

$(TARGET): CMP.o
	gcc CMP.o -lm -o $(TARGET)
	
CMP.o: CMP.c
	gcc -c CMP.c

.PHONY: clean
clean:
	rm -f $(TARGET) *.o *.bin *.rpt *.exe *.out