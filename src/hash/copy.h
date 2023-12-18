#ifndef __COPY_H__
#define __COPY_H__

#include "../lib_ecc_config.h"
#include "../words/words.h"
#include "../utils/utils.h"

#define COPY256_SIZE  32

typedef struct {
	u64 copied_bytes;
	/* Internal buffer to handle updates in a block */
	u8 buffer[COPY256_SIZE];
} copy256_context;

void copy256_init(copy256_context *ctx);
void copy256_update(copy256_context *ctx, const u8 *input, u32 ilen);
void copy256_final(copy256_context *ctx, u8 output[COPY256_SIZE]);
void copy256_scattered(const u8 **inputs, const u32 *ilens,
		      u8 output[COPY256_SIZE]);
void copy256(const u8 *input, u32 ilen, u8 output[COPY256_SIZE]);

#endif /* __COPY_H__ */
