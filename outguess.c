/*
 * Outguess - a Universal Steganograpy Tool for
 *
 * Copyright (c) 1999-2001 Niels Provos <provos@citi.umich.edu>
 * Features
 * - preserves frequency count based statistics
 * - multiple data embedding
 * - PRNG driven selection of bits
 * - error correcting encoding
 * - modular architecture for different selection and embedding algorithms
 */

/*
 * Copyright (c) 1999-2001 Niels Provos <provos@citi.umich.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *      This product includes software developed by Niels Provos.
 * 4. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <ctype.h>
#include <fcntl.h>
#include <unistd.h>
#include <math.h>
#include <time.h>

#include "config.h"

#include "arc.h"
#include "outguess.h"
#include "jpg.h"
#include "iterator.h"
#include "string.h"

#ifndef MAP_FAILED
/* Some Linux systems are missing this */
#define MAP_FAILED (void *)-1
#endif /* MAP_FAILED */

bitmap bm;

void *
checkedmalloc(size_t n)
{
	void *p;

	if (!(p = malloc(n)))
	{
		fprintf(stderr, "checkedmalloc: not enough memory\n");
		exit(1);
	}

	return p;
}

u_int32_t
steg_retrbyte(bitmap *bitmap, int bits, iterator *iter)
{
	u_int32_t i = ITERATOR_CURRENT(iter);
	int where;
	u_int32_t tmp = 0;

	for (where = 0; where < bits; where++)
	{
		tmp |= (TEST_BIT(bitmap->bitmap, i) ? 1 : 0) << where;

		i = iterator_next(iter, bitmap);
	}

	return tmp;
}

u_char *
steg_retrieve(u_int *len, bitmap *bitmap, iterator *iter, struct arc4_stream *as)
{
	u_int32_t n;
	int i;
	u_int32_t origlen;
	u_int16_t seed;
	u_int datalen;
	u_char *buf;
	u_int8_t *tmpbuf;

	datalen = 4;
	encode_data(NULL, &datalen, NULL);
	tmpbuf = checkedmalloc(datalen);

	for (i = 0; i < datalen; i++)
		tmpbuf[i] = steg_retrbyte(bitmap, 8, iter);

	buf = decode_data(tmpbuf, &datalen, as);

	if (datalen != 4)
	{
		// fprintf(stderr, "Steg retrieve: wrong data len: %d\n", datalen);
		// exit(1);
		return NULL;
	}

	free(tmpbuf);

	seed = buf[0] | (buf[1] << 8);
	origlen = datalen = buf[2] | (buf[3] << 8);

	free(buf);

	if (datalen > bitmap->bytes)
	{
		// fprintf(stderr, "Extracted datalen is too long: %d > %d\n", datalen, bitmap->bytes);
		// exit(1);
		return NULL;
	}

	buf = checkedmalloc(datalen);

	iterator_seed(iter, bitmap, seed);

	n = 0;
	while (datalen > 0)
	{
		iterator_adapt(iter, bitmap, datalen);

		// Sometimes, iter->skipmod becomes 0,
		// resulting in a floatingpoint exception
		if (iter->skipmod == 0)
		{
			buf[n++] = 0;
			datalen--;
			continue;
		}

		buf[n++] = steg_retrbyte(bitmap, 8, iter);
		datalen--;
	}

	*len = origlen;
	return buf;
}

/* graphic file handling routines */

u_char *
encode_data(u_char *data, u_int *len, struct arc4_stream *as)
{
	u_int j, datalen = *len;
	u_char *encdata;

	if (data == NULL)
	{
		*len = datalen;
		return NULL;
	}
	encdata = checkedmalloc(datalen * sizeof(u_char));

	/* Encryption */
	for (j = 0; j < datalen; j++)
		encdata[j] = data[j] ^ arc4_getbyte(as);

	*len = datalen;

	return encdata;
}

u_char *
decode_data(u_char *encdata, u_int *len, struct arc4_stream *as)
{
	u_int j, enclen = *len, declen;
	u_char *data;

	for (j = 0; j < enclen; j++)
		encdata[j] = encdata[j] ^ arc4_getbyte(as);

	data = checkedmalloc(enclen * sizeof(u_char));
	declen = enclen;
	memcpy(data, encdata, declen);

	*len = declen;
	return data;
}

void read_bitmap()
{
	image *image = jpg_handler.read(stdin);

	jpg_handler.get_bitmap(&bm, image, STEG_RETRIEVE);

	free(image->img);
	free(image);
}

void free_bitmap()
{
	free(bm.bitmap);
	free(bm.locked);
}

u_char *outguess(u_char *key, u_int *datalen)
{
	struct arc4_stream as, tas;
	iterator iter;
	unsigned char *encdata;

	/* Initialize random data stream */
	arc4_initkey(&as, "Encryption", key, strlen((char *)key));
	tas = as;

	iterator_init(&iter, &bm, key, strlen((char *)key));

	encdata = steg_retrieve(datalen, &bm, &iter, &as);
	if (encdata == NULL)
	{
		return NULL;
	}

	u_char *data = decode_data(encdata, datalen, &tas);

	free(encdata);

	return data;
}

unsigned char b26_list[] = "abcdefghijklmnopqrstuvwxyz";
const char *b26_encode(unsigned long val)
{
	static char result[8] = {'a', 'a', 'a', 'a', 'a', 'a', 'a', '\0'};
	static unsigned long previous = 0;
	int i;

	if (previous != val)
	{
		previous = val;
		for (i = 6; i >= 0; i--)
		{
			result[i] = b26_list[val % 26];
			val = val / 26;
		}
		result[7] = 0;
	}

	for (i = 0; i < 6; i++)
		if (result[i] != b26_list[0])
			return result + i;

	return result + 6;
}

void brute_words()
{
	static char clearline[6] = {0x0d, 0x1b, '[', '2', 'K', '\0'};
	// static char bold[5] = {0x1b, '[', '1', 'm', '\0'};

	int total = pow(26, 5);
	char filename[70];

	fprintf(stderr, "a ... %s\n", b26_encode(total - 1));
	fprintf(stderr, "%d Iterations\n", total);

	clock_t begin = clock();
	for (int i = 0; i < total; i++)
	{
		u_int datalen;
		u_char *key = (u_char *)b26_encode(i);
		u_char *data = outguess(key, &datalen);
		fprintf(stderr, "%s%s", clearline, key);
		if (data == NULL)
		{
			continue;
		}
		if (datalen >= 8)
		{
			//printf("%s %d\n", key, datalen);
			bool isJPEG = data[0] == 0xff && data[1] == 0xd8 && data[datalen - 2] == 0xff && data[datalen - 1] == 0xd9;
			bool isPNG = data[0] == 0x89 && data[1] == 0x50 && data[2] == 0x4e && data[3] == 0x47 && data[4] == 0x0d && data[5] == 0x0a && data[6] == 0x1a && data[7] == 0x0a;
			if (isJPEG || isPNG)
			{
				if (isJPEG)
				{
					sprintf(filename, "%s.jpg", key);
				}
				else
				{
					sprintf(filename, "%s.png", key);
				}
				printf("%s %d\n", filename, datalen);
				FILE *fout = fout = fopen(filename, "wb");
				if (fout == NULL)
				{
					fprintf(stderr, "Can't open output file");
					exit(1);
				}
				fwrite(data, datalen, sizeof(u_char), fout);
				fclose(fout);
			}
		}
		free(data);
	}
	clock_t end = clock();
	double time_spent = (double)(end - begin);
	fprintf(stderr, "Time: %fs\n", time_spent / CLOCKS_PER_SEC);
}

void brute_dates()
{
	char buff[70];
	char buff_debug[70];
	char filename[70];
	// 112313091989
	// struct tm starttime = {
	// 	.tm_hour = 11,
	// 	.tm_min = 23,
	// 	.tm_mday = 13,
	// 	.tm_mon = 8,
	// 	.tm_year = 1989 - 1900};
	struct tm starttime = {
		.tm_hour = 0,
		.tm_min = 0,
		.tm_mday = 1,
		.tm_mon = 0,
		.tm_year = 1980 - 1900};
	time_t current_timestamp = mktime(&starttime);

	clock_t begin = clock();
	for (int i = 0; i < 525600 * 45; i++)
	{
		struct tm *currenttime = localtime(&current_timestamp);
		strftime(buff, sizeof buff, "%H%M%d%m%Y", currenttime);

		if (currenttime->tm_hour == 0 && currenttime->tm_min == 0 && currenttime->tm_mday == 1)
		{
			strftime(buff_debug, sizeof buff, "%d.%m.%Y", currenttime);
			printf("%s\n", buff_debug);
		}

		u_int datalen;
		u_char *data = outguess((u_char *)buff, &datalen);
		current_timestamp += 60;
		if (data == NULL)
		{
			continue;
		}
		// printf("%s %02x %02x %d\n", buff, data[0], data[1], datalen);
		if (datalen >= 8)
		{
			bool isJPEG = data[0] == 0xff && data[1] == 0xd8 && data[datalen - 2] == 0xff && data[datalen - 1] == 0xd9;
			bool isPNG = data[0] == 0x89 && data[1] == 0x50 && data[2] == 0x4e && data[3] == 0x47 && data[4] == 0x0d && data[5] == 0x0a && data[6] == 0x1a && data[7] == 0x0a;
			if (isJPEG || isPNG)
			{
				if (isJPEG)
				{
					sprintf(filename, "%s.jpg", buff);
				}
				else
				{
					sprintf(filename, "%s.png", buff);
				}
				printf("%s %d\n", filename, datalen);
				FILE *fout = fout = fopen(filename, "wb");
				if (fout == NULL)
				{
					fprintf(stderr, "Can't open output file");
					exit(1);
				}
				fwrite(data, datalen, sizeof(u_char), fout);
				fclose(fout);
			}
		}
		free(data);
		current_timestamp += 60;
	}
	clock_t end = clock();
	double time_spent = (double)(end - begin);
	fprintf(stderr, "Brute time: %fs\n", time_spent / CLOCKS_PER_SEC);
}

int main(int argc, char **argv)
{
	// u_char *key = (u_char *)argv[1];
	// u_char *out_name = (u_char *)argv[2];

	read_bitmap();
	brute_words();
	// brute_dates();

	// clock_t begin = clock();

	// u_int datalen;
	// u_char *data = outguess(key, &datalen);
	// fprintf(stderr, "Extracted usable bits: %d bits\n", bm.bits);
	// fprintf(stderr, "Extracted file size: %d\n", datalen);

	// clock_t end = clock();
	// double time_spent = (double)(end - begin);
	// fprintf(stderr, "Time: %fs\n", time_spent / CLOCKS_PER_SEC);

	// FILE *fout = fout = fopen((char *)out_name, "wb");
	// if (fout == NULL)
	// {
	// 	fprintf(stderr, "Can't open output file '%s': ", out_name);
	// 	exit(1);
	// }
	// fwrite(data, datalen, sizeof(u_char), fout);

	// free(data);

	free_bitmap();
}
