/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: matmul_c_core.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/numerical/matmul/C/0/0/double_blocked/matmul_c_core.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: blocked Matrix Multiplication (C)
 *******************************************************************/

#include "stdio.h"
#include "stdlib.h"
#include <string.h>
#include "matmul.h"
#include "interface.h"

#define min(C,A,B) if (A<B) C=A; else C=B;

void multaijk_(double *a, double *b, double *c, int *size, int *blocksize);
void multaikj_(double *a, double *b, double *c, int *size, int *blocksize);
void multajik_(double *a, double *b, double *c, int *size, int *blocksize);
void multajki_(double *a, double *b, double *c, int *size, int *blocksize);
void multakji_(double *a, double *b, double *c, int *size, int *blocksize);
void multakij_(double *a, double *b, double *c, int *size, int *blocksize);

double getlanguage_(void);

void multaijk_(double *a, double *b, double *c, int *size, int *blocksize)
{
  int i, j, k,i0 ,j0 ,k0 ,imin, jmin, kmin;
  int s = *size;
  int block= *blocksize;
	//IDL(-1, printf("1 %i %i\n",s,block));
  for (i0 = 0; i0 < s; i0=i0+block)
  {
  	min(imin,i0+block,s);
  	//printf("%i is the min of %i and %i\n",imin,i0+block,s);
    for (j0 = 0; j0 < s; j0=j0+block)
    {
  		min(jmin,j0+block,s);
      for (k0 = 0; k0 < s; k0=k0+block)
      {
  			min(kmin,k0+block,s);
  			for (i = i0; i < imin; i++)
   				for (j = j0; j < jmin; j++)
   			  	for (k = k0; k < kmin; k++)
          	{
        	 		c[ i * s + j ] = c[ i * s + j ] + a[ i * s + k ] * b[ k * s + j ];
           	}
      }
    }
	}
}

void multaikj_(double *a, double *b, double *c, int *size, int *blocksize)
{
  int i, j, k,i0 ,j0 ,k0 ,imin, jmin, kmin;
  int s = *size;
  int block= *blocksize;
	//IDL(-1, printf("2 %i %i\n",s,block));
  for (i0 = 0; i0 < s; i0=i0+block)
  {
  	min(imin,i0+block,s);
     for (k0 = 0; k0 < s; k0=k0+block)
    {
  		min(kmin,k0+block,s);
  	  for (j0 = 0; j0 < s; j0=j0+block)
      {
  			min(jmin,j0+block,s);
  			for (i = i0; i < imin; i++)
   			  for (k = k0; k < kmin; k++)
   					for (j = j0; j < jmin; j++)
          	{
        	 		c[ i * s + j ] = c[ i * s + j ] + a[ i * s + k ] * b[ k * s + j ];
           	}
      }
    }
	}
}

void multajik_(double *a, double *b, double *c, int *size, int *blocksize)
{
  int i, j, k,i0 ,j0 ,k0 ,imin, jmin, kmin;
  int s = *size;
  int block= *blocksize;
	//IDL(-1, printf("3 %i %i\n",s,block));
  for (j0 = 0; j0 < s; j0=j0+block)
  {
  	min(jmin,j0+block,s);
  	for (i0 = 0; i0 < s; i0=i0+block)
  	{
  		min(imin,i0+block,s);
     	for (k0 = 0; k0 < s; k0=k0+block)
   		{
  			min(kmin,k0+block,s);
   			for (j = j0; j < jmin; j++)
  				for (i = i0; i < imin; i++)
   				  for (k = k0; k < kmin; k++)
          	{
        	 		c[ i * s + j ] = c[ i * s + j ] + a[ i * s + k ] * b[ k * s + j ];
           	}
      }
    }
	}
}

void multajki_(double *a, double *b, double *c, int *size, int *blocksize)
{
  int i, j, k,i0 ,j0 ,k0 ,imin, jmin, kmin;
  int s = *size;
  int block= *blocksize;
	//IDL(-1, printf("4 %i %i\n",s,block));
  for (j0 = 0; j0 < s; j0=j0+block)
  {
  	min(jmin,j0+block,s);
    for (k0 = 0; k0 < s; k0=k0+block)
   	{
  		min(kmin,k0+block,s);
  		for (i0 = 0; i0 < s; i0=i0+block)
  		{
  			min(imin,i0+block,s);
   			for (j = j0; j < jmin; j++)
   				for (k = k0; k < kmin; k++)
  					for (i = i0; i < imin; i++)
          	{
        	 		c[ i * s + j ] = c[ i * s + j ] + a[ i * s + k ] * b[ k * s + j ];
           	}
      }
    }
	}
}
void multakij_(double *a, double *b, double *c, int *size, int *blocksize)
{
  int i, j, k,i0 ,j0 ,k0 ,imin, jmin, kmin;
  int s = *size;
  int block= *blocksize;
	//IDL(-1, printf("5 %i %i\n",s,block));
  for (k0 = 0; k0 < s; k0=k0+block)
  {
  	min(kmin,k0+block,s);
  	for (i0 = 0; i0 < s; i0=i0+block)
  	{
  		min(imin,i0+block,s);
  		for (j0 = 0; j0 < s; j0=j0+block)
  		{
  			min(jmin,j0+block,s);
   			for (k = k0; k < kmin; k++)
  				for (i = i0; i < imin; i++)
   					for (j = j0; j < jmin; j++)
          	{
        	 		c[ i * s + j ] = c[ i * s + j ] + a[ i * s + k ] * b[ k * s + j ];
           	}
      }
    }
	}
}

void multakji_(double *a, double *b, double *c, int *size, int *blocksize)
{
  int i, j, k,i0 ,j0 ,k0 ,imin, jmin, kmin;
  int s = *size;
  int block= *blocksize;
	//IDL(-1, printf("6 %i %i\n",s,block));
  for (k0 = 0; k0 < s; k0=k0+block)
  {
  	min(kmin,k0+block,s);
  	for (j0 = 0; j0 < s; j0=j0+block)
  	{
  		min(jmin,j0+block,s);
  		for (i0 = 0; i0 < s; i0=i0+block)
  		{
  			min(imin,i0+block,s);
   			for (k = k0; k < kmin; k++)
   				for (j = j0; j < jmin; j++)
  					for (i = i0; i < imin; i++)
          	{
        	 		c[ i * s + j ] = c[ i * s + j ] + a[ i * s + k ] * b[ k * s + j ];
           	}
      }
    }
	}
}

double getlanguage_()
{
  return 1.0;
}


