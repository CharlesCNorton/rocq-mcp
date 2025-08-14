/**
 * Input validators for tool arguments
 */

export class ValidationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ValidationError';
  }
}

export function validateString(value: any, name: string, required: boolean = true): string | undefined {
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

export function validateBoolean(value: any, name: string, required: boolean = false): boolean | undefined {
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

export function validateNumber(value: any, name: string, required: boolean = false, min?: number, max?: number): number | undefined {
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

export function validateArray(value: any, name: string, required: boolean = false): any[] | undefined {
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

export function validateEnum<T>(value: any, name: string, validValues: T[], required: boolean = false): T | undefined {
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

export function validatePath(value: any, name: string, required: boolean = true): string | undefined {
  const path = validateString(value, name, required);
  
  if (path && path.includes('..')) {
    throw new ValidationError(`${name} cannot contain '..' for security reasons`);
  }
  
  return path;
}