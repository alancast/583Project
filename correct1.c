// test 1:  no conflict, no uses of LOAD
#include "stdio.h"

int a[100];
int b[100];

void function2(int i){
    if (i%2 == 0){
	printf("function2 called with even value\n");
    } else {
	printf("function2 called with odd value\n");
    }
}

void function1(int j){
    if (j%3 == 0){
	int val = j*3;
	function2(val);
    } else {
	int val = (j+3)*2;
	printf("val = %d\n", val);
    }
}

int main()
{
    int x = 0,i;
    int *ptra = a;
    for (i=0;i<100;i++){
	a[i] = i;
	if (i > 32){
	    function1(i);
	}
    }
    for (i=0;i<100;i++){
	if (i > 999){ //   case 1: don't need reload 
	    a[i+1] = 1;
	}
	b[i] = a[97];
    }
    printf ("%d, %d, %d\n",b[97],b[98],b[99]);
    return 0;
}
