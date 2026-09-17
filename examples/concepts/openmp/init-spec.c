// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPinit
//:: tools

/*
  The use of omp_get_thread_num is currently unsupported.
*/

// gcc -fopenmp -c zero-spec.c

#include <omp.h>
#include <stdio.h>

/*@
  requires len > 0;
  context \pointer(a, len, write);
@*/
void init(int len, int a[], int ppid) {
#pragma omp parallel for private(i)
  for (int i = 0; i < len; i++)
  /*@
    context len>0 ** \pointer_index(a, i, write);
  @*/
  {
    int iam = omp_get_thread_num();
    a[i] = ppid * 100 + iam;
  }
}
