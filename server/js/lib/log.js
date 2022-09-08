const winston = require('winston');

// var appRoot = require('app-root-path');

const log = winston.createLogger({
  level: 'info',
  exitOnError: false,
  format: winston.format.combine(
    winston.format.timestamp(),
    winston.format.json()
  ),
  transports: [
    new winston.transports.Console(),
    // new winston.transports.File({ filename: `${appRoot}/logs/debug.log` }),
    new winston.transports.File({ filename: `/var/log/browserquest/debug.log` }),
  ],
});

module.exports = log;
