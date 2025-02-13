/*
 * SPDX-FileCopyrightText: 2023 Fox Crypto B.V.
 * SPDX-License-Identifier: MIT
 *
 * SPDX-FileContributor: Frans van Dorsselaer
 */

/**
 * @file
 * @brief
 * The configurable CMake options that affect the public API.
 *
 * @details
 * There is no need to include this header explicitly. Instead, include either verification.h or signing.h.
 */

#pragma once

#ifndef XMSS_XMSS_CONFIG_H_INCLUDED
/** @private @brief Include guard. */
#define XMSS_XMSS_CONFIG_H_INCLUDED

/**
 * @brief
 * Indicates whether the compiler supports `_Static_assert()`.
 *
 * @details
 * This option is automatically detected by CMake.
 *
 * @see XMSS_STATIC_ASSERT
 */
#define XMSS_CAN_USE_STATIC_ASSERT 0

/**
 * @brief
 * Indicates whether the compiler supports `__extension__ _Static_assert()`.
 *
 * @details
 * This option is automatically detected by CMake.
 *
 * @see XMSS_STATIC_ASSERT
 */
#define XMSS_CAN_USE_EXTENSION_STATIC_ASSERT 1

/**
 * @brief
 * Indicates whether the library is built with signing support.
 *
 * @details
 * By default, signing support is enabled. This macro is defined with the value 0 if you compile the library with
 * ```
 * cmake -DXMSS_ENABLE_SIGNING=OFF
 * ```
 */
#define XMSS_ENABLE_SIGNING 1

/**
 * @brief
 * The major version of the library headers.
 *
 * @see #XMSS_LIBRARY_VERSION
 * @see xmss_library_get_version()
 */
#define XMSS_LIBRARY_VERSION_MAJOR 2

/**
 * @brief
 * The minor version of the library headers.
 *
 * @see #XMSS_LIBRARY_VERSION
 * @see xmss_library_get_version()
 */
#define XMSS_LIBRARY_VERSION_MINOR 0

/**
 * @brief
 * The patch version of the library headers.
 *
 * @see #XMSS_LIBRARY_VERSION
 * @see xmss_library_get_version()
 */
#define XMSS_LIBRARY_VERSION_PATCH 0

#endif /* !XMSS_XMSS_CONFIG_H_INCLUDED */
