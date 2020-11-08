#include<stdio.h>
#include<limits.h>
/*@ requires 0 <= n <= INT_MAX;
    ensures \result > 0;
*/
float sum_pattern(int n)
{
	float sum=0,i=1;
/*@ loop invariant 1 <= i <= n;
  @ loop assigns sum,i; 
*/
	while (i <= n)
	{
	 sum += (1/i);
	i++;
	}
	//@ assert i == n;
	return sum;
}
void main()
{
	float result;
	result = sum_pattern(10);
}
