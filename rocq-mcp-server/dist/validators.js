/**
 * Input validators for tool arguments
 */
export class ValidationError extends Error {
    constructor(message) {
        super(message);
        this.name = 'ValidationError';
    }
}
export function validateString(value, name, required = true) {
    if (value === undefined || value === null) {
        if (required) {
            throw new ValidationError(`${name} is required`);
        }
        return undefined;
    }
    if (typeof value !== 'string') {
        throw new ValidationError(`${name} must be a string`);
    }
    if (required && value.trim().length === 0) {
        throw new ValidationError(`${name} cannot be empty`);
    }
    return value;
}
export function validateBoolean(value, name, required = false) {
    if (value === undefined || value === null) {
        if (required) {
            throw new ValidationError(`${name} is required`);
        }
        return undefined;
    }
    if (typeof value !== 'boolean') {
        throw new ValidationError(`${name} must be a boolean`);
    }
    return value;
}
export function validateNumber(value, name, required = false, min, max) {
    if (value === undefined || value === null) {
        if (required) {
            throw new ValidationError(`${name} is required`);
        }
        return undefined;
    }
    if (typeof value !== 'number' || isNaN(value)) {
        throw new ValidationError(`${name} must be a number`);
    }
    if (min !== undefined && value < min) {
        throw new ValidationError(`${name} must be at least ${min}`);
    }
    if (max !== undefined && value > max) {
        throw new ValidationError(`${name} must be at most ${max}`);
    }
    return value;
}
export function validateArray(value, name, required = false) {
    if (value === undefined || value === null) {
        if (required) {
            throw new ValidationError(`${name} is required`);
        }
        return undefined;
    }
    if (!Array.isArray(value)) {
        throw new ValidationError(`${name} must be an array`);
    }
    return value;
}
export function validateEnum(value, name, validValues, required = false) {
    if (value === undefined || value === null) {
        if (required) {
            throw new ValidationError(`${name} is required`);
        }
        return undefined;
    }
    if (!validValues.includes(value)) {
        throw new ValidationError(`${name} must be one of: ${validValues.join(', ')}`);
    }
    return value;
}
export function validatePath(value, name, required = true) {
    const path = validateString(value, name, required);
    if (path && path.includes('..')) {
        throw new ValidationError(`${name} cannot contain '..' for security reasons`);
    }
    return path;
}
//# sourceMappingURL=validators.js.map