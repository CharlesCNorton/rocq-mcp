import winston from 'winston';
import * as path from 'path';
export function createLogger() {
    return winston.createLogger({
        level: process.env.LOG_LEVEL || 'info',
        format: winston.format.combine(winston.format.timestamp(), winston.format.errors({ stack: true }), winston.format.json()),
        transports: [
            new winston.transports.File({
                filename: path.join(process.cwd(), 'mcp-coq-server.log'),
                maxsize: 5242880, // 5MB
                maxFiles: 5,
            }),
            new winston.transports.Console({
                format: winston.format.combine(winston.format.colorize(), winston.format.simple()),
                // Always log to stderr to avoid interfering with JSON-RPC on stdout
                stderrLevels: ['error', 'warn', 'info', 'verbose', 'debug', 'silly'],
                silent: process.env.NODE_ENV === 'production',
            }),
        ],
    });
}
//# sourceMappingURL=logger.js.map