#include<iostream>

int main(void){
    float x;
    int y;
    x = 2.0;
    y = 0;
    if (y != 0){
        x = 2.0;
    }
    else{
        y = 1;
    }
    while(x==0.0){
        y = y + 1;
    }
    return y;
}