// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPsum
//:: tools

/*

This is correct openMP code, but it is difficult to encode into PVL.
The problem is that there are len logical thread that are
mapped to an unknown number of physical threads.
The local variables tmp are physical thread-local variables.
They satisfy the invariant that the sum of all tmp
variables is the sum of the processed array elements.


*/
#include <omp.h>
#include <stdio.h>

/*@
  context_everywhere a != NULL;
  requires \pointer_length(a) >= len;
@*/
int sum(int len, int a[]) {
  int i;
  int res = 0;
#pragma omp parallel private(i) reduction(+ : res)
  {
    int tmp = 0;
#pragma omp for nowait
    for (i = 0; i < len; i++)
    /*@
      context a != NULL;
      context Perm(a[i],1);
    @*/
    {
      tmp += a[i];
      a[i] = 0;
    }
    res += tmp;
  }
  return res;
}
