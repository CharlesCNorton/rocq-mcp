/**
 * Input validators for tool arguments
 */
export declare class ValidationError extends Error {
    constructor(message: string);
}
export declare function validateString(value: any, name: string, required?: boolean): string | undefined;
export declare function validateBoolean(value: any, name: string, required?: boolean): boolean | undefined;
export declare function validateNumber(value: any, name: string, required?: boolean, min?: number, max?: number): number | undefined;
export declare function validateArray(value: any, name: string, required?: boolean): any[] | undefined;
export declare function validateEnum<T>(value: any, name: string, validValues: T[], required?: boolean): T | undefined;
export declare function validatePath(value: any, name: string, required?: boolean): string | undefined;
//# sourceMappingURL=validators.d.ts.map