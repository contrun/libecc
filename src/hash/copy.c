#include "../lib_ecc_config.h"

#include "copy.h"

/* Init hash function */
void copy256_init(copy256_context *ctx)
{
	MUST_HAVE(ctx != NULL);

	ctx->copied_bytes = 0;
}

/* Update hash function */
void copy256_update(copy256_context *ctx, const u8 *input, u32 ilen)
{
	u32 bytes_to_copy = ilen;
	u16 left_bytes;

	MUST_HAVE((ctx != NULL) && (input != NULL));

	/* Nothing to process, return */
	if (ilen == 0) {
		return;
	}

	/* Get what's left in our local buffer */
	left_bytes = COPY256_SIZE - (ctx->copied_bytes & 0x3F);

	if (bytes_to_copy >= left_bytes) {
    bytes_to_copy = left_bytes;
	}
	local_memcpy(ctx->buffer + ctx->copied_bytes, input, bytes_to_copy);
  ctx->copied_bytes += bytes_to_copy;
	return;
}

/* Finalize */
void copy256_final(copy256_context *ctx, u8 output[COPY256_SIZE])
{
	MUST_HAVE((ctx != NULL) && (output != NULL));
  // The ec_self_tests here may send less than COPY256_SIZE bytes
	// We always send COPY256_SIZE to outputs, even if library users
  // didn't send COPY256_SIZE to us.
	local_memcpy(output, ctx->buffer, COPY256_SIZE);
}

void copy256_scattered(const u8 **inputs, const u32 *ilens,
		      u8 output[COPY256_SIZE])
{
	copy256_context ctx;
	int pos = 0;

	copy256_init(&ctx);

	while (inputs[pos] != NULL) {
		copy256_update(&ctx, inputs[pos], ilens[pos]);
		pos += 1;
	}

	copy256_final(&ctx, output);
}
